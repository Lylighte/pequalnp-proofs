'use strict';
const fs=require('node:fs'),path=require('node:path');
const {materialize}=require('./tree-cut.cjs'),{roots,extend}=require('./tree-extension.cjs'),{apply}=require('../plane920-math/plane-orbits.js'),{search}=require('./effective-cut.cjs');
const d=path.join(__dirname,'unrestricted'),total=Number(process.argv[2]),h=Number(process.argv[3]),n=Number(process.argv[4]||5),from=Number(process.argv[5]||0),end=Number(process.argv[6]||1e8);
const fn=path.join(d,'tree-next-'+[total,h,n,from,end].join('-')+'.jsonl'),done=new Set((fs.existsSync(fn)?fs.readFileSync(fn,'utf8'):'').trim().split('\n').filter(Boolean).map(l=>JSON.parse(l).i));
const tag='tree-cut-'+[total,h,n].join('-')+'-';
const permuted=(a,p)=>a.map(t=>apply(t,p)).sort((a,b)=>a-b).toString();
function restart(r){
 const [gs,ps]=materialize(r.p);
 const stab=roots[r.p[0]].stab.filter(p=>ps.slice(3).every(([a,b])=>{
   const x=permuted(a,p),y=permuted(b,p);return (x===a.toString()&&y===b.toString())||(x===b.toString()&&y===a.toString());}));
 let checked=0,orbits=0;const unresolved=[];
 extend(gs,stab,(g,pair,nextStab,weight,i,j)=>{
   checked+=weight;orbits++;
   const v=search([...gs,g],[...ps,pair],total-13-h,h-n-1,30000);
   if(v.open)unresolved.push({p:[...r.p,i,j],weight,capped:v.capped});
 });
 return {i:r.i,p:r.p,stab:stab.length,checked,orbits,unresolved};
}
for(const f of fs.readdirSync(d).filter(f=>f.startsWith(tag))){
 const lines=fs.readFileSync(path.join(d,f),'utf8').trim().split('\n').filter(Boolean);
 for(const l of lines){
   const r=JSON.parse(l);if(!r.open||done.has(r.i)||r.i<from||r.i>=end)continue;
   fs.appendFileSync(fn,JSON.stringify(restart(r))+'\n');done.add(r.i);
 }
}

