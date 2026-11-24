'use strict';
const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict');
const {lines}=require('./plane-symmetry.cjs'),{encode}=require('./slice-program.cjs');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const dir=path.join(__dirname,'slice-runs'),checks=[];
for(const n of [8,9]){
 for(const {u} of JSON.parse(fs.readFileSync(path.join(dir,n+'-4.json'),'utf8')).cases){
  const pts=Array.from({length:13},(_,i)=>i).filter(i=>u&(1<<i));
  const gates=[],out=[];
  for(const L of lines){const a=pts.map((p,i)=>L&(1<<p)?i:-1).filter(i=>i>=0);if(a.length<3)continue;
   let x=a[0];for(let j=1;j<a.length-1;j++){gates.push([x,a[j]].sort((p,q)=>q-p));x=n+gates.length-1;}
   out.push([a.at(-1),x]);}
  const m=encode(u,gates.length), unit=[];
  gates.forEach((g,j)=>g.forEach((raw,b)=>m.ports[j][b].forEach((id,i)=>unit.push((i===raw?id:-id)+' 0'))));
  out.forEach(([x,y],j)=>{const yes=m.decoders[j].defs.find(e=>e.lo===x&&e.hi===y);assert(yes);unit.push(yes.choice+' 0');});
  const cnf=m.cnf.replace(/^p cnf (\d+) (\d+)/,(all,v,l)=>'p cnf '+v+' '+(Number(l)+unit.length))+unit.join('\n')+'\n';
  const f=path.join(dir,'direct-control.cnf');fs.writeFileSync(f,cnf);
  const r=cp.spawnSync(solver,['-q',f],{encoding:'utf8',timeout:15000,maxBuffer:4000000,windowsHide:true});assert.equal(r.status,10);
  checks.push({u,n,helpers:gates.length,targets:out.length,status:'SAT'});
 }
}
fs.writeFileSync(path.join(dir,'direct-controls.json'),JSON.stringify(checks,null,2));console.log(JSON.stringify(checks));
