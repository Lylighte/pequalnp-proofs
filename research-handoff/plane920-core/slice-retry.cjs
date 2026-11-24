'use strict';
const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),zlib=require('node:zlib');
const {group,lines}=require('./plane-symmetry.cjs'),{encode}=require('./slice-encode.cjs'),{checkProof}=require('../plane920-search/stream-rup.cjs');
const bin=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const dir=path.join(__dirname,'slice-runs');fs.mkdirSync(dir,{recursive:true});
const n=Number(process.argv[2]||8), helpers=Number(process.argv[3]||3), limit=Number(process.argv[4]||3000);
const pop=Array.from({length:8192},(_,s)=>s.toString(2).replaceAll('0','').length);
const map=(u,p)=>p.reduce((m,t,i)=>m|((u&(1<<i))?1<<t:0),0);
const orbits=[];
for(let u=0;u<8192;u++)if(pop[u]===n&&!orbits.some(o=>o.includes(u)))orbits.push([...new Set(group.map(p=>map(u,p)))].sort((a,b)=>a-b));
const sum=orbits.reduce((s,o)=>s+o.length,0);assert.equal(sum,pop.filter(x=>x===n).length);
const file=path.join(dir,n+'-'+helpers+'.json');
const state=fs.existsSync(file)?JSON.parse(fs.readFileSync(file,'utf8')):{n,helpers,cases:[]};
const hash=s=>crypto.createHash('sha256').update(s).digest('hex');
async function run(){
 for (const orbit of orbits){
  const u=orbit[0],old=state.cases.find(s=>s.u===u);
  if(old && !['UNKNOWN','SAT-SEED'].includes(old.verdict))continue;
  const pts=Array.from({length:13},(_,i)=>1<<i).filter(x=>x&u),remap=s=>pts.reduce((r,p,i)=>r|((p&s)?1<<i:0),0);
  const targets=lines.map(L=>remap(L)).filter(t=>pop[t]>=3);
  const seed=[...new Set([...targets,...targets.flatMap(t=>pts.map((_,i)=>t&~(1<<i))),...Array.from({length:1<<n},(_,i)=>i).filter(i=>pop[i]<=2)])].sort((a,b)=>a-b);
  const cfile=path.join(dir,n+'-'+helpers+'-'+u+'.cnf'),pfile=cfile+'.lrat';
  let result;
  for(const rows of [undefined]){
   const dimacs=encode(u,helpers,rows);fs.writeFileSync(cfile,dimacs);const t=Date.now();
   const r=cp.spawnSync(bin,['-q','--no-elim','--no-block','--no-condition','--lrat','--no-binary',cfile,pfile],{encoding:'utf8',windowsHide:true,timeout:limit,maxBuffer:4e6});
   result={u,orbitSize:orbit.length,targets:targets.length,rows:rows?.length||'full',satMs:Date.now()-t,sha256:hash(dimacs)};
   if(r.status===20){
     const proof=await checkProof(dimacs,pfile);const data=fs.readFileSync(pfile);assert(proof.empty);
     fs.writeFileSync(pfile+'.gz',zlib.gzipSync(data));fs.unlinkSync(pfile);
     Object.assign(result,{verdict:'UNSAT-replayed',proof:proof.sha256,add:proof.add,bytes:data.length});break;
   }
   if(r.status===10){
     result.verdict=rows?'SAT-SEED':'SAT-model';
     if(!rows){fs.writeFileSync(cfile+'.model',r.stdout);break;}
   } else {result.verdict='UNKNOWN'; if(!rows)break;}
  }
  state.cases=state.cases.filter(x=>x.u!==u).concat(result);fs.writeFileSync(file,JSON.stringify(state,null,2));
  console.log(JSON.stringify(result));
 }
}
run().catch(e=>{console.error(e);process.exitCode=1});
