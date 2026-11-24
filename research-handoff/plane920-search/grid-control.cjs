const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const {test}=require('./local-exact.cjs'),{checkProof}=require('./stream-rup.cjs');
const lines=[[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8]],ids=[0,1,2,3,4,5],solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
(async()=>{
 const rows=[],runs=[];
 for(let iter=0;iter<7;iter++){
   const r=test(ids,10,{lines,rowBudget:3,rows,order:true,live:false,conflicts:350000,ms:18000});
   runs.push({status:r.status,ms:r.ms,tested:r.rows,bad:r.bad?.length});
   if(r.status==='UNSAT')break;
   assert.equal(r.status,'SAT');assert(r.bad.length);rows.push(...r.bad.filter(v=>!rows.includes(v)).slice(0,12));
 }
 assert.equal(runs.at(-1).status,'UNSAT');
 const cnf=fs.readFileSync(path.join(__dirname,'partial-0-1-2-3-4-5-10.cnf'),'utf8');
 fs.writeFileSync(path.join(__dirname,'grid10.cnf'),cnf);
 const p=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary','grid10.cnf','grid10.lrat'],{cwd:__dirname,windowsHide:true,timeout:25000});
 assert.equal(p.status,20);const proof=await checkProof(cnf,path.join(__dirname,'grid10.lrat'));
 const sha=crypto.createHash('sha256').update(cnf).digest('hex');
 const audit={lines,n:10,rows,runs,cnfHash:sha,proof};
 fs.writeFileSync(path.join(__dirname,'grid10-result.json'),JSON.stringify(audit,null,2)+'\n');
 console.log(audit);
})().catch(e=>{console.error(e);process.exitCode=1});
