'use strict';
const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process');
const crypto=require('node:crypto'),zlib=require('node:zlib'),assert=require('node:assert/strict');
const {encode}=require('./slice-program.cjs'),{checkProof}=require('../plane920-search/stream-rup.cjs');
const mask=Number(process.argv[2]),k=Number(process.argv[3]),timeout=Number(process.argv[4]||15000);
const floors=(process.argv[5]||'0,2,4,5').split(',').map(Number);
const facts={lines:Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,j)=>m|1<<((i+j)%13),0)).filter((_,i)=>mask&(1<<i)),floors};
const u=facts.lines.reduce((a,b)=>a|b),pts=Array.from({length:13},(_,i)=>1<<i).filter(p=>u&p);
const remap=t=>pts.reduce((m,p,i)=>m|Number(Boolean(t&p))<<i,0),targets=facts.lines.map(remap);
const n=pts.length,pc=Array.from({length:1<<n},(_,i)=>i.toString(2).replaceAll('0','').length);
const domain=pc.flatMap((s,i)=>s===4?[i]:[]);
const dir=path.join(__dirname,'slice-runs'),stem=path.join(dir,'family-'+mask+'-'+k+'-'+floors.join(''));
const bin=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const file=stem+'.json',cnf=stem+'.cnf',proof=stem+'.lrat',hash=a=>crypto.createHash('sha256').update(a).digest('hex');
const rows=new Set(targets.flatMap(t=>[t,...pts.map((_,i)=>t&~(1<<i))]));
let start=0;
if(fs.existsSync(file)){const prev=JSON.parse(fs.readFileSync(file));if(['UNSAT-replayed','SAT-verified'].includes(prev.verdict)){console.log(prev.verdict);process.exit(0);}prev.rows.forEach(r=>rows.add(r));start=prev.step+1;}
(async()=>{
for(let step=start;step<start+20;step++){
  const ordered=[...rows].sort((a,b)=>a-b),m=encode(u,k,ordered,facts),t=Date.now();
  fs.writeFileSync(cnf,m.cnf);
  const run=cp.spawnSync(bin,['-q','--plain','--lrat','--no-binary',cnf,proof],{encoding:'utf8',timeout,windowsHide:true,maxBuffer:8e6});
  const rec={mask,k,step,floors,rows:ordered,cnf:hash(m.cnf),millis:Date.now()-t};
  if(run.status===20){
    rec.verdict='UNSAT-replayed';rec.check=await checkProof(m.cnf,proof);assert(rec.check.empty);
    fs.writeFileSync(proof+'.gz',zlib.gzipSync(fs.readFileSync(proof)));fs.unlinkSync(proof);
  }else if(run.status===10){
    const trueVars=new Set(run.stdout.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(' ').map(Number)));
    const gates=m.ports.map(g=>g.map(s=>s.reduce((a,v,j)=>a|(Number(trueVars.has(v))<<j),0)));
    const dec=m.decoders.map(d=>({...d.defs.find(c=>trueVars.has(c.choice)),target:d.s}));
    function bad(r){let w=r;gates.forEach(([a,b],j)=>{if((a&w)&&(b&w))w|=1<<(n+j);});return dec.map(({lo,hi,target})=>Boolean((w&(1<<lo))&&(w&(1<<hi)))!==(target===r));}
    assert(ordered.every(r=>!bad(r).some(Boolean)));
    const failures=domain.map(r=>[r,bad(r)]).filter(x=>x[1].some(Boolean));
    if(!failures.length){rec.verdict='SAT-verified';rec.gates=gates;rec.outputs=dec;}
    else{
      for(let j=0;j<targets.length;j++){
        const f=failures.filter(x=>x[1][j]);if(!f.length)continue;
        for(let i=0;i<Math.min(3,f.length);i++)rows.add(f[Math.floor(f.length*i/3)][0]);
      }
      rec.rows=[...rows].sort((a,b)=>a-b);rec.verdict='partial';rec.violations=failures.length;
    }
  }else rec.verdict='UNKNOWN';
  fs.writeFileSync(file,JSON.stringify(rec,null,2)+'\n');
  console.log(mask,k,step,ordered.length,rec.verdict,rec.millis,rec.check?.add||'');
  if(rec.verdict!=='partial')break;
}
})().catch(e=>{console.error(e);process.exitCode=1;});

