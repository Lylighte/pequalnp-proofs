const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {table,raw,loc,lines,univ,pm}=require('./three-or-five-lines.cjs');
function solve(mask,row,budget=5,allMode=false){
 const ws=[],ids=new Map(),reg=w=>{if(!ids.has(w)){ids.set(w,ws.length);ws.push(w);}return ids.get(w);};
 const flags=[table(row.firstOr),table(row.t)],prods=[univ,...flags,flags[0]&flags[1]];
 for(let i=0;i<13;i++)if(mask&1<<i)for(let z=lines[i];z;z=(z-1)&lines[i])for(const x of prods)
   if(pm(x&table([z]))&mask)reg(x&table([z]));
 for(const v of prods)if(pm(v)&mask)reg(v);
 const roots=[row.firstOr.map(m=>ids.get(table([m]))),[ids.get(table(row.a)),ids.get(table(row.b))]];
 const named=flags.map(v=>ids.get(v)),forced=[...new Set(roots.flat())].filter(q=>!raw.includes(ws[q])&&!named.includes(q));
 const N=ws.length,initial=Array.from({length:N},(_,i)=>i).filter(i=>raw.includes(ws[i]));
 const pairs=Array.from({length:N},()=>new Int16Array(N).fill(-1)),target=new Int16Array(N);
 for(let a=0;a<N;a++){
   target[a]=loc.indexOf(ws[a])<0?0:1<<loc.indexOf(ws[a]);
   for(let b=0;b<N;b++)pairs[a][b]=ids.get(ws[a]&ws[b])??-1;
 }
 const seen=new Set();let count=0,solution=null;const solutions=new Map();
 function rec(ops,avail,stage,covered){
   const has=new Uint8Array(N);for(const a of avail)has[a]=1;
   while(stage<2&&roots[stage].every(x=>has[x])){
     const q=named[stage++];if(!has[q]){avail.push(q);has[q]=1;for(const a of avail){const p=pairs[a][q];if(p>=0)covered|=target[p];}}
   }
   if((covered&mask)===mask&&stage===2){solution={ops,stage};if(allMode){const ids=ops.map(q=>q[2]).sort((a,b)=>a-b);solutions.set(ids.join(','),ids.map(i=>ws[i].toString(16)));return false;}return true;}
   const left=budget-ops.length,needed=forced.filter(q=>!has[q]);if(left===0||needed.length>left)return false;
   const key=ops.map(q=>q[2]).sort((a,b)=>a-b).join(',');if(seen.has(key))return false;seen.add(key);count++;
   const only=needed.length===left,seenChild=new Set();
   for(let i=0;i<avail.length;i++)for(let j=0;j<i;j++){
     const a=avail[i],b=avail[j],q=pairs[a][b];
     if(q<0||has[q]||seenChild.has(q)||only&&!needed.includes(q))continue;
     seenChild.add(q);
     let c=covered|target[q];for(const z of avail){const v=pairs[z][q];if(v>=0)c|=target[v];}
     if(rec([...ops,[a,b,q]],[...avail,q],stage,c))return true;
   }
   return false;
 }
 rec([],initial,0,0);
 return {count,solution,...(allMode?{all:[...solutions.values()]}:{})};
}
if(require.main===module){
 const source=JSON.parse(fs.readFileSync(path.join(__dirname,'two-or-three-lines-all.json'))),results=[];
 for(const s of source){
  const checks=s.live.map(row=>solve(s.mask,row));
  results.push({mask:s.mask,states:checks.reduce((n,v)=>n+v.count,0),checked:checks.length,live:checks.map((x,i)=>x.solution?{i,...x}:null).filter(Boolean)});
 }
 fs.writeFileSync(path.join(__dirname,'two-or-three-lines-physical.json'),JSON.stringify(results)+'\n');
 console.log(results);
 if(process.argv.includes('--cores')){
   const cores=results.flatMap((r,k)=>r.live.map(({i})=>({i,row:source[k].live[i],out:solve(r.mask,source[k].live[i],5,true).all})));
   fs.writeFileSync(path.join(__dirname,'three-line-five-cores.json'),JSON.stringify(cores));
 }
}
module.exports={solve};
