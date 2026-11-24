const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict'),zlib=require('node:zlib'),crypto=require('node:crypto');
const {make,patterns,allowed,cross,evaluate}=require('./disjoint-four-cross.cjs');
const {checkProof}=require('./stream-rup.cjs');
const records=require('./disjoint-four-cross-results.json');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const dir=path.join(__dirname,'replay-disjoint-cross');fs.mkdirSync(dir,{recursive:true});
const pathFor=f=>path.join(dir,f), tally=pathFor('receipts.json');
const result=fs.existsSync(tally)?JSON.parse(fs.readFileSync(tally)):{receipts:{},unverified:{}};
const codes=new Set();
for(let c=0;c<10000;c++){
 const ts=String(c).padStart(4,'0').split('').map(Number);
 if(ts.some((t,i)=>t>=4&&ts.indexOf(t)!==i))continue;
 codes.add(ts.sort((a,b)=>a-b).join(','));
}
assert.equal(codes.size,400);assert.deepEqual(codes,new Set(patterns.map(p=>p.join(','))));
const positiveControls=[0,1,2,3],standard=positiveControls.map(i=>[1<<(3*i+1),1<<(3*i+2)]);
for(const m of allowed)assert(!evaluate(standard,positiveControls,m).bad);
for(const m of cross)assert.equal(evaluate(standard,positiveControls,m).active,0);
const keys=[...codes].sort();
const jobs=[];
for(const key of keys){
 const pat=key.split(',').map(Number);
 if(key==='3,3,3,3'){
   for(const mask of [9,17,18])for(const helper of [0,1,2]){
     jobs.push({key:key+'_'+mask+'_'+helper,pat,pinned:{mask,helper},rows:records.rows});
   }
 }else{
   const r=records.results[key];assert(['UNSAT','analytic'].includes(r.status));
   jobs.push({key,pat,rows:records.rows.slice(0,r.rows||records.rows.length)});
 }
}
const hardOnly=process.argv.includes('--hard'),softOnly=process.argv.includes('--soft'),timeLimit=Number(process.argv.find(x=>/^\d+$/.test(x))||55000);
const hash=data=>crypto.createHash('sha256').update(data).digest('hex');
(async()=>{
 const start=Date.now();
 if(process.argv.includes('--audit')){
   const spool=pathFor('archive-audit.lrat');let checked=0,additions=0;
   for(const {key,pat,pinned,rows} of jobs){
     const rec=result.receipts[key],{dimacs}=make(pat,rows,true,pinned);
     assert(rec);assert.equal(hash(dimacs),rec.cnfSha256);
     if(rec.baseEmpty)assert(dimacs.split('\n').some(l=>l.trim()==='0'));
     else{
       const plain=zlib.gunzipSync(fs.readFileSync(pathFor(rec.name)));
       assert.equal(hash(plain),rec.proofSha256);assert.equal(plain.length,rec.proofBytes);
       fs.writeFileSync(spool,plain);
       const got=await checkProof(dimacs,spool);
       assert(got.empty);assert.equal(got.add,rec.add);additions+=got.add;
     }
     checked++;
   }
   fs.unlinkSync(spool);
   const audit={jobs:checked,patterns:codes.size,checkedAdditions:additions,positiveControlRows:allowed.length,ms:Date.now()-start};
   fs.writeFileSync(pathFor('archive-audit.json'),JSON.stringify(audit,null,2)+'\n');console.log(audit);return;
 }
 for(const {key,pat,pinned,rows} of jobs){
   if(Date.now()-start>timeLimit)break;
   if((hardOnly&&!pinned)||(softOnly&&pinned)||result.receipts[key])continue;
   const {dimacs}=make(pat,rows,true,pinned),cnf=pathFor('active.cnf'),proof=pathFor('active.lrat');
   fs.writeFileSync(cnf,dimacs);
   if(dimacs.split('\n').some(line=>line.trim()==='0')){
     result.receipts[key]={rows:rows.length,cnfSha256:hash(dimacs),baseEmpty:true,add:0,compressed:0};
     fs.writeFileSync(tally,JSON.stringify(result)+'\n');continue;
   }
   const run=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',cnf,proof],{encoding:'utf8',windowsHide:true,timeout:pinned?8000:4000});
   if(run.status===20){
     const verified=await checkProof(dimacs,proof),proofBytes=fs.statSync(proof).size;
     const name=key.replaceAll(',','')+'.lrat.gz',gzip=zlib.gzipSync(fs.readFileSync(proof));
     fs.writeFileSync(pathFor(name),gzip);
     result.receipts[key]={rows:rows.length,cnfSha256:hash(dimacs),name,proofBytes,compressed:gzip.length,...verified};
     delete result.unverified[key];
   }else result.unverified[key]={code:run.status,reason:run.error?.code};
   fs.writeFileSync(tally,JSON.stringify(result)+'\n');
 }
 const rr=Object.values(result.receipts);
 console.log({jobs:jobs.length,verified:rr.length,proofAdds:rr.reduce((n,v)=>n+v.add,0),compressed:rr.reduce((n,v)=>n+v.compressed,0),unverified:result.unverified,ms:Date.now()-start});
})().catch(e=>{console.error(e);process.exitCode=1;});
