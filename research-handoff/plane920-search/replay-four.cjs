const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),cp=require('node:child_process'),assert=require('node:assert/strict'),zlib=require('node:zlib');
const {pipeline}=require('node:stream/promises'),{checkProof}=require('./stream-rup.cjs'),{pop,model}=require('./local-exact.cjs');
const auditDir=path.join(__dirname,'replay'),solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
fs.mkdirSync(auditDir,{recursive:true});
const kind=process.argv[2],phase=process.argv[3]||'all',budget=Number(process.argv[4]||90)*1000;
assert(['quad','transverse'].includes(kind));
const src=require(kind==='quad'?'./quadrilateral-complete.json':'./three-concurrent-plus-fourth-complete.json');
const ops=src.complete.map(x=>x.ops).sort((a,b)=>a-b);
const expected=Array.from({length:128},(_,i)=>i).filter(x=>pop(x)>=2&&pop(x)<=5);assert.deepEqual(ops,expected);
const shape=kind==='quad'?src.complete.slice().sort((a,b)=>Number(b.core)-Number(a.core)||b.ms-a.ms):
 src.complete.slice().sort((a,b)=>b.ms-a.ms);
const file=path.join(auditDir,kind+'-receipts.json'),log=fs.existsSync(file)?JSON.parse(fs.readFileSync(file,'utf8')):
 {mode:kind,opsComplete:true,byMultiplicity:[2,3,4,5].map(m=>[m,ops.filter(x=>pop(x)===m).length]),certificates:[],attempts:[]};
const stop=Date.now()+budget;
(async()=>{
 for(const x of shape){
   if(Date.now()>stop)break;
   if(phase==='hard'&&!x.core||log.certificates.some(z=>z.ops===x.ops))continue;
   const core=kind==='transverse'||!!x.core;
   const m=model(src.ids,11,{ops:x.ops,order:true,sensitivity:true,core,requireTwoOr:kind==='transverse',
     privateBound:kind==='transverse',rows:x.rows});
   const dimacs='p cnf '+m.vars+' '+m.cnf.length+'\n'+m.cnf.map(c=>c.join(' ')+' 0').join('\n')+'\n';
   const digest=crypto.createHash('sha256').update(dimacs).digest('hex');assert.equal(digest,x.sha256);
   const cfile=path.join(auditDir,kind+'-active.cnf'),pfile=path.join(auditDir,kind+'-active.lrat');
   fs.writeFileSync(cfile,dimacs);const started=Date.now();
   const p=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',cfile,pfile],{encoding:'utf8',timeout:22000,windowsHide:true});
   if(p.status!==20){
     log.attempts.push({ops:x.ops,status:p.status,error:p.error?.code,ms:Date.now()-started});
     fs.writeFileSync(file,JSON.stringify(log,null,2)+'\n');continue;
   }
   const solveMs=Date.now()-started,checked=await checkProof(dimacs,pfile),finish=Date.now();
   // Save the five hardest streams compressed; all other streams can be
   // reproduced from their exact DIMACS and proof hashes.
   let archivedBytes=null;
   if(kind==='quad'&&x.core){
     const dest=path.join(auditDir,'quad-'+x.ops+'.lrat.gz');
     await pipeline(fs.createReadStream(pfile),zlib.createGzip({level:1}),fs.createWriteStream(dest));
     archivedBytes=fs.statSync(dest).size;
   }
   log.certificates.push({ops:x.ops,core,cnfSha256:digest,proofBytes:fs.statSync(pfile).size,archivedBytes,
     solveMs,checkMs:finish-started-solveMs,...checked});
   fs.writeFileSync(file,JSON.stringify(log,null,2)+'\n');
 }
 console.log({kind,phase,certified:log.certificates.length,attempts:log.attempts.length,total:ops.length});
})().catch(e=>{console.error(e);process.exitCode=1;});
