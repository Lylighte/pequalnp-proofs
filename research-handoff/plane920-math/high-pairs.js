"use strict";
const fs=require("node:fs"),path=require("node:path");
const {lines,weight:w,perm,apply}=require("./plane-orbits");
const pts=Array.from({length:13},(_,i)=>i),all=8191;
const maps=perm.map(p=>lines.map(l=>lines.indexOf(apply(l,p))));
const maj=Array.from({length:8192},(_,r)=>pts.reduce((m,i)=>{
 if(!(r&(1<<i)))return m;
 let a=lines[i];for(const j of pts)if(j!==i&&(r&(1<<j)))a&=~lines[j];
 return m|(a?1<<i:0);
},0));
const seen=new Set(),rr=[];
for(let a=0;a<=all;a++){
 if(seen.has(a))continue;
 const group=[],orbit=new Set();for(const p of maps){const b=apply(a,p);orbit.add(b);if(a===b)group.push(p);}
 for(const b of orbit)seen.add(b);
 if(w[a]<2||w[maj[a]]<3)continue;
 const seenB=new Set();
 for(let b=0;b<=all;b++){
  if(seenB.has(b))continue;
  const setB=new Set(group.map(p=>apply(b,p))); for(const bb of setB)seenB.add(bb);
  if(w[b]<2||w[all^(a|b)]>2||w[maj[b]]>w[maj[a]])continue;
  // Any endpoint pair must include 'a' since its inactive complement has >=6 rows.
  // There are at most four edges. With b also inactive on >=6,
  // the only possible edge is a-b, isolated exactly if they co-occur on one row.
  if(w[a]>7)throw Error("private-row table");
  let potential;
  if(w[b]<=7){potential=w[a&b]===1?a&b:0;}
  else potential=a;
  const already=maj[a]|maj[b],need=all^already;
  const allowedPairs=w[b]<=7?1:4;
  if(w[need&~potential]>3||w[need]>3+Math.min(allowedPairs,w[need&potential]))continue;
  rr.push({a,b,privateA:maj[a],privateB:maj[b],afterRaw:w[need],orbitA:orbit.size,orbitB:setB.size});
 }
}
const hist={};for(const r of rr){
 const k=[w[r.a],w[r.b],w[r.privateA],w[r.privateB]].join("-");hist[k]=(hist[k]||0)+1;
}
fs.writeFileSync(path.join(__dirname,"small-core","high-pairs.json"),JSON.stringify({hist,rr},null,2)+"\n");
console.log(JSON.stringify({representatives:rr.length,hist}));
