'use strict';
const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),zlib=require('node:zlib');
const {encode}=require('./slice-program.cjs'),{checkProof}=require('../plane920-search/stream-rup.cjs');
const dir=path.join(__dirname,'slice-runs'),bin=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const u=Number(process.argv[2]),k=Number(process.argv[3]),timeout=Number(process.argv[4]||15000);
const pop=x=>x.toString(2).replaceAll('0','').length;
const tag='cegis-'+u+'-'+k, out=path.join(dir,tag+'.json'),cnf=path.join(dir,tag+'.cnf'),pf=cnf+'.lrat';
const init=encode(u,k,[]),domain=Array.from({length:1<<init.n},(_,i)=>i).filter(r=>pop(r)<=4);
let rows=new Set(init.targets.flatMap(t=>[t,...Array.from({length:init.n},(_,j)=>t&~(1<<j))]));
if(fs.existsSync(out)){const old=JSON.parse(fs.readFileSync(out,'utf8'));if(old.status==='UNSAT-replayed'){console.log(tag,'already verified');process.exit(0);}old.rows.forEach(x=>rows.add(x));}
const hash=s=>crypto.createHash('sha256').update(s).digest('hex');
async function main(){
 for(let step=0;step<25;step++){
  const ordered=[...rows].sort((a,b)=>a-b),m=encode(u,k,ordered);
  fs.writeFileSync(cnf,m.cnf);
  const res=cp.spawnSync(bin,['-q','--plain','--lrat','--no-binary',cnf,pf],{encoding:'utf8',windowsHide:true,timeout,maxBuffer:5000000});
  const receipt={u,k,rows:ordered,step,cnf:hash(m.cnf)};
  if(res.status===20){
    const pr=await checkProof(m.cnf,pf);assert(pr.empty);const proof=fs.readFileSync(pf);
    fs.writeFileSync(pf+'.gz',zlib.gzipSync(proof));fs.unlinkSync(pf);
    Object.assign(receipt,{status:'UNSAT-replayed',add:pr.add,bytes:proof.length,sha256:hash(proof)});
  } else if(res.status===10){
    const trueVar=new Set(res.stdout.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(' ').map(Number)));
    const gates=m.ports.map(g=>g.map(side=>side.reduce((mask,v,j)=>mask|(trueVar.has(v)?1<<j:0),0)));
    const outW=m.decoders.map(dec=>({...dec.defs.find(e=>trueVar.has(e.choice)),target:dec.s}));
    const violations=domain.filter(r=>{
      let w=r;gates.forEach(([a,b],i)=>{if((w&a)&&(w&b))w|=1<<(m.n+i);});
      return outW.some(({lo,hi,target})=>pop(r)<=pop(target)&& Boolean((w&(1<<lo))&&(w&(1<<hi)))!==(r===target));
    });
    assert(ordered.every(r=>!violations.includes(r)));receipt.numMiss=violations.length;
    if(!violations.length)Object.assign(receipt,{status:'SAT-verified',gates,outW});
    else {receipt.status='partial';violations.slice(0,12).forEach(v=>rows.add(v));receipt.rows=[...rows];}
  }else receipt.status='unknown';
  fs.writeFileSync(out,JSON.stringify(receipt,null,2));console.log(tag,step,receipt.status,ordered.length,receipt.numMiss??receipt.add??'');
  if(receipt.status!=='partial')break;
 }
}
main().catch(e=>{console.error(e);process.exitCode=1});
