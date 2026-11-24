const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),cp=require('node:child_process'),zlib=require('node:zlib');
const {encode,code,verify,rows}=require('./common-two.cjs'),{checkProof}=require('./stream-rup.cjs');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe'),dir=path.join(__dirname,'common-two-first');fs.mkdirSync(dir,{recursive:true});
const perm=[];
for(const swap of [0,1])for(const e of [0,1])for(const f of [0,1]){
 const p=Array.from({length:6},(_,i)=>{const g=i/3|0,j=i%3;return 3*(g^swap)+(j===0?0:((g?f:e)?3-j:j));});
 perm.push(Array.from({length:64},(_,m)=>p.reduce((s,x,i)=>s|((m&1<<i)?1<<x:0),0)));
}
const reps=new Map();
for(let a=0;a<64;a++)for(let b=0;b<64;b++){
 const key=Math.min(...perm.map(p=>Math.min(64*p[a]+p[b],64*p[b]+p[a])));
 if(!reps.has(key))reps.set(key,[]);reps.get(key).push(64*a+b);
}
(async()=>{
 const report=[],r=rows(6),passed=[];
 for(const [key,orbit] of reps){
   const s=[key>>6,key%64],{dimacs,...vars}=encode(6,4,[0,0],[],r,true,false,undefined,s);
   const c=path.join(dir,'temp.cnf'),p=path.join(dir,'temp.lrat');fs.writeFileSync(c,dimacs);
   const run=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',c,p],{encoding:'utf8',windowsHide:true,timeout:1500});
   const rec={s,orbitSize:orbit.length,status:run.status===10?'SAT':run.status===20?'UNSAT':'UNKNOWN'};
   if(run.status===20){const ck=await checkProof(dimacs,p),gz=zlib.gzipSync(fs.readFileSync(p));fs.writeFileSync(path.join(dir,key+'.lrat.gz'),gz);rec.add=ck.add;}
   if(run.status===10){const model=code(run.stdout,vars);assert.deepEqual(model.gate[0],s);assert.equal(verify(model,6,[0,0],[],r).length,0);rec.model=model;passed.push(...orbit);}
   report.push(rec);
 }
 fs.writeFileSync(path.join(dir,'results.json'),JSON.stringify({report,passed})+'\n');
 console.log({reps:reps.size,passed:passed.length,status:report.reduce((o,r)=>(o[r.status]=(o[r.status]||0)+1,o),{}),satShapes:report.filter(r=>r.status==='SAT').map(r=>r.s)});
})().catch(e=>{console.error(e);process.exitCode=1;});
