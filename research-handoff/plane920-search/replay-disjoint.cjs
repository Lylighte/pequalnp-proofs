const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),cp=require('node:child_process'),assert=require('node:assert/strict'),zlib=require('node:zlib');
const {make,patterns}=require('./disjoint-patterns.cjs'),{checkProof}=require('./stream-rup.cjs');
const dir=path.join(__dirname,'replay-disjoint');fs.mkdirSync(dir,{recursive:true});
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const src=require('./disjoint-pattern-results.json'),unsat=new Map(src.results.filter(x=>x.status==='UNSAT').map(r=>[r.pat.join(),r]));
const expected=new Set();
// Form all labeled choices independently, then quotient by permutation of
// the four disjoint triples. A helper-helper pair can serve only one output.
for(let code=0;code<6**4;code++){
 let v=code;const p=[];for(let i=0;i<4;i++){p.push(v%6);v=Math.floor(v/6);}
 if(p.some((x,i)=>x>=3&&p.indexOf(x)!==i))continue;
 expected.add(p.sort((a,b)=>a-b).join());
}
assert.equal(expected.size,66);assert.deepEqual([...expected].sort(),[...unsat.keys()].sort());
const controls=Array.from({length:4096},(_,m)=>m).filter(m=>m.toString(2).replaceAll('0','').length<=3);
const targets=[7,56,448,3584];
for(const m of controls){
 const w=Array.from({length:12},(_,v)=>!!(m&1<<v));
 for(let i=0;i<4;i++)w.push(w[3*i+1]&&w[3*i+2]);
 for(let i=0;i<4;i++)assert.equal(w[3*i]&&w[12+i],m===targets[i]);
}
(async()=>{
 const rec=[];
 for(const e of unsat.values()){
   const {dimacs}=make(e.pat,e.tested),hash=crypto.createHash('sha256').update(dimacs).digest('hex');
   assert.equal(hash,e.sha256);
   const c=path.join(dir,'active.cnf'),pf=path.join(dir,'active.lrat');
   fs.writeFileSync(c,dimacs);
   const probe=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',c,pf],{encoding:'utf8',windowsHide:true,timeout:16000});
   assert.equal(probe.status,20);
   const verified=await checkProof(dimacs,pf),size=fs.statSync(pf).size;
   const compressed=zlib.gzipSync(fs.readFileSync(pf),{level:6});
   const filename=e.pat.join('')+'.lrat.gz';fs.writeFileSync(path.join(dir,filename),compressed);
   rec.push({pat:e.pat,rowCount:e.tested.length,cnfSha256:hash,filename,proofBytes:size,storedBytes:compressed.length,...verified});
 }
 const summary={patterns:rec.length,controlRows:controls.length,add:rec.reduce((s,r)=>s+r.add,0),
    bytes:rec.reduce((s,r)=>s+r.proofBytes,0),storedBytes:rec.reduce((s,r)=>s+r.storedBytes,0)};
 fs.writeFileSync(path.join(dir,'receipts.json'),JSON.stringify({summary,rec},null,2)+'\n');console.log(summary);
})().catch(e=>{console.error(e);process.exitCode=1;});
