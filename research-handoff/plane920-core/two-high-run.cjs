'use strict';
const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict');
const zlib=require('node:zlib'),crypto=require('node:crypto');
const {cnfFor,lines,pc}=require('./two-high-cnf.cjs'),{checkProof}=require('../plane920-search/stream-rup.cjs');
const bin=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const dir=path.join(__dirname,'unrestricted','two-high');fs.mkdirSync(dir,{recursive:true});
const options=[1984,2016,3008,4032,4040,8128].flatMap(b=>[[63,b],[b,63]]);
const all=Array.from({length:8192},(_,i)=>i).filter(i=>pc[i]<=4),index=new Map(lines.map((m,i)=>[m,i]));
const hash=x=>crypto.createHash('sha256').update(x).digest('hex');
async function run(a,b,timeout){
  const stem=path.join(dir,a+'-'+b),out=stem+'.json',input=stem+'.cnf',proof=stem+'.lrat';
  const old=fs.existsSync(out)?JSON.parse(fs.readFileSync(out,'utf8')):null;
  if(old&&['UNSAT-replayed','SAT-checked'].includes(old.verdict))return;
  const rows=new Set(old?.rows||lines.flatMap(l=>[l,...lines.map((_,p)=>l&~(1<<p))]));
  for(let it=0;it<12;it++){
    const ordered=[...rows].sort((x,y)=>x-y),{cnf,ports,dec}=cnfFor(a,b,ordered),t=Date.now();
    fs.writeFileSync(input,cnf);
    const r=cp.spawnSync(bin,['-q','--plain','--no-binary','--lrat',input,proof],{encoding:'utf8',timeout,windowsHide:true,maxBuffer:8e6});
    const rec={a,b,ms:Date.now()-t,rows:ordered,cnf:hash(cnf),verdict:'UNKNOWN'};
    if(r.status===20){
      rec.check=await checkProof(cnf,proof);assert(rec.check.empty);rec.verdict='UNSAT-replayed';
      fs.writeFileSync(proof+'.gz',zlib.gzipSync(fs.readFileSync(proof)));fs.unlinkSync(proof);
    }else if(r.status===10){
      const set=new Set(r.stdout.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(' ').map(Number)));
      const gates=ports.map(g=>g.map(side=>side.reduce((m,v,i)=>m|Number(set.has(v))<<i,0)));
      const outs=dec.map(opts=>opts.find(o=>set.has(o.yes)));assert(outs.every(Boolean));
      const failures=[];
      for(const row of all){
        let w=row;for(let i=0;i<6;i++)if((w&gates[i][0])&&(w&gates[i][1]))w|=1<<(13+i);
        const bad=outs.some(({lo,hi},i)=>Boolean((w>>lo&1)&&(w>>hi&1))!==(row===lines[i])||
          (hi<17 && pc[row]<=3 && Boolean(w>>hi&1)!==(row===(lines[i]^(1<<lo)))));
        const high=[a,b].some((mask,i)=>pc[row]<=3?Boolean(w>>(17+i)&1):
          index.has(row)&&Boolean(w>>(17+i)&1)!==Boolean(mask&(1<<index.get(row))));
        if(bad||high)failures.push(row);
      }
      assert(failures.every(r=>!rows.has(r)));
      if(!failures.length){rec.verdict='SAT-checked';rec.gates=gates;rec.outs=outs;}
      else{rec.verdict='partial';for(let i=0;i<Math.min(13,failures.length);i++)rows.add(failures[Math.floor(i*failures.length/Math.min(13,failures.length))]);rec.rows=[...rows];rec.violations=failures.length;}
    }
    fs.writeFileSync(out,JSON.stringify(rec,null,2)+'\n');console.log(a,b,ordered.length,rec.verdict,rec.ms);
    if(rec.verdict!=='partial')return;
  }
}
(async()=>{for(const i of process.argv[2].split(',').map(Number))await run(...options[i],Number(process.argv[3]||12000));})().catch(e=>{console.error(e);process.exitCode=1;});

