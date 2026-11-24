'use strict';
const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict');
const {cnfFor,lines,pc}=require('./two-high-cnf.cjs'),{encode}=require('./slice-program.cjs');
const {checkProof}=require('../plane920-search/stream-rup.cjs');
const dir=path.join(__dirname,'unrestricted','two-high'),bin=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
function units(cnf,more){
  const ix=cnf.indexOf('\n'),[p,f,n,k]=cnf.slice(0,ix).split(' ');
  return [p,f,n,Number(k)+more.length].join(' ')+cnf.slice(ix)+more.map(l=>l+' 0\n').join('');
}
if(process.argv[2]==='control'){
  const rows=Array.from({length:8192},(_,i)=>i).filter(i=>pc[i]<=4),m=cnfFor(1,2,rows,3);
  const pins=[[1,0],[9,3],[2,1],[10,4],[14,13],[16,15]],us=[];
  m.ports.forEach((pair,h)=>pair.forEach((side,s)=>side.forEach((v,j)=>us.push(j===pins[h][s]?v:-v))));
  const dimacs=units(m.cnf,us),file=path.join(dir,'positive.cnf');fs.writeFileSync(file,dimacs);
  const r=cp.spawnSync(bin,['-q',file],{encoding:'utf8',windowsHide:true,maxBuffer:4e6});assert.equal(r.status,10);
  let checked=0;
  for(const row of rows){let w=row;for(let h=0;h<6;h++)if(pins[h].every(j=>w&(1<<j)))w|=1<<(13+h);
    assert.equal(Boolean(w&(1<<17)),row===lines[0]);assert.equal(Boolean(w&(1<<18)),row===lines[1]);checked++;}
  fs.writeFileSync(path.join(dir,'positive.json'),JSON.stringify({pins,checked,exit:r.status})+'\n');
  console.log('control rows',checked);process.exit(0);
}
(async()=>{
 const [a,b]=process.argv.slice(2,4).map(Number),orig=require(path.join(dir,a+'-'+b+'.json')),rows=orig.rows;
 const m=encode(8191,6,rows),idx=new Map(lines.map((l,i)=>[l,i])),us=[];
 rows.forEach((r,i)=>{if(pc[r]<=3||idx.has(r))for(const [k,mask]of [a,b].entries())
   us.push(idx.has(r)&&(mask&(1<<idx.get(r)))?m.vals[i][17+k]:-m.vals[i][17+k]);});
 const dimacs=units(m.cnf,us),stem=path.join(dir,'relaxed-'+a+'-'+b),file=stem+'.cnf',pf=stem+'.lrat';
 fs.writeFileSync(file,dimacs);const r=cp.spawnSync(bin,['-q','--plain','--lrat','--no-binary',file,pf],{windowsHide:true,timeout:14000,maxBuffer:8e6});
 const rec={a,b,rows:rows.length,verdict:r.status===20?'UNSAT':r.status===10?'SAT':'UNKNOWN'};
 if(r.status===20)rec.check=await checkProof(dimacs,pf);
 fs.writeFileSync(stem+'.json',JSON.stringify(rec)+'\n');console.log(rec);
})().catch(e=>{console.error(e);process.exitCode=1;});

