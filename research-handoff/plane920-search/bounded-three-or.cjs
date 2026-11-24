const fs=require('node:fs'),path=require('node:path');
const {table,mult,join,orbits,raw,loc,lines,univ,pm,pc,perm}=require('./three-or-five-lines.cjs');
const mono=Array.from({length:8192},(_,i)=>i).filter(i=>pc[i]===1||pc[i]===2),norm=k=>k.join(',');
const rawProds=[{v:univ,s:8191,p:0},...mono.map(p=>({v:table([p]),s:pm(table([p])),p}))];
function terms(prev){
 const choices=new Map(),pr=[[0]];for(const f of prev)for(const s of [...pr])pr.push(mult(f,s));
 for(const {p} of rawProds)for(let i=0;i<pr.length;i++){
   if(!p&&!i)continue;const v=mult([p],pr[i]),key=norm(v);
   if(!choices.has(key))choices.set(key,{t:v,sign:lines.reduce((s,L,i)=>s|(v.some(m=>(m&L)===m)?1<<i:0),0)});
 }return [...choices.values()].filter(x=>x.sign);
}
function next(gs){
 const all=terms(gs),found=new Map(),prev=new Set(gs.map(norm));
 for(let i=0;i<all.length;i++)for(let j=0;j<i;j++){
   const a=all[i],b=all[j];if(!(a.sign&~b.sign)||!(b.sign&~a.sign))continue;
   const t=join(a.t,b.t),key=norm(t);if(!prev.has(key))found.set(key,t);
 }return found;
}
const first=orbits(next([]),perm);
const roots=[];
for(const a of first)for(const b of orbits(next([a.t]),a.stab))roots.push([a.t,b.t]);
module.exports={roots,terms,rawProds};
if(require.main===module)console.log({first:first.length,roots:roots.length,buckets:first.map(a=>({first:a.t,size:a.size,stab:a.stab.length}))});
