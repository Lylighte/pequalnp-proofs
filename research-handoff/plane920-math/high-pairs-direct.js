"use strict";
const fs=require("node:fs"),path=require("node:path");
const {weight:w,lines,perm,apply}=require("./plane-orbits.js"),pts=Array.from({length:13},(_,i)=>i),all=8191;
const maps=perm.map(p=>lines.map(l=>lines.indexOf(apply(l,p))));
const pm=Array.from({length:8192},(_,r)=>{
 let a=0;
 for(let p=0;p<13;p++){
  const hit=lines.reduce((m,l,i)=>m|(((r>>i&1)&&(l>>p&1))?1<<i:0),0);
  if(w[hit]===1)a|=hit;
 }
 return a;
});
const reps=JSON.parse(fs.readFileSync(path.join(__dirname,"small-core","high-pairs.json"))).rr;
const key=(a,b)=>a*8192+b,seen=new Set();
for(const r of reps)for(const pp of maps)seen.add(key(apply(r.a,pp),apply(r.b,pp)));
const hist={},nrep={},samples=[];let rawCandidates=0;
for(let a=0;a<=all;a++){
 const k=w[pm[a]];hist[w[a]]=(hist[w[a]]||0);hist[w[a]]=Math.max(hist[w[a]],k);
 if(k<3)continue;if(w[a]>7)throw Error("private histogram");
 for(let b=0;b<=all;b++){
  if(w[b]<2||w[pm[b]]>k||w[all^(a|b)]>2)continue;
  const may=w[b]<=7?(w[a&b]===1?(a&b):0):a,cap=w[b]<=7?1:4;
  const remainder=all^(pm[a]|pm[b]);
  if(w[remainder&~may]>3||w[remainder]>3+Math.min(cap,w[remainder&may]))continue;
  rawCandidates++;
  if(!seen.has(key(a,b)))samples.push([a,b]);
  const K=[w[a],w[b],w[pm[a]],w[pm[b]]].join("-");nrep[K]=(nrep[K]||0)+1;
 }
}
if(samples.length||seen.size!==rawCandidates)throw Error(JSON.stringify({samples:samples.slice(0,12),rawCandidates,seen:seen.size}));
const result={privateMaxBySize:hist,labeledHigherPrivateFirst:rawCandidates,orbitUnion:seen.size,bySize:nrep};
fs.writeFileSync(path.join(__dirname,"small-core","high-pairs-direct.json"),JSON.stringify(result,null,2)+"\n");console.log(result);
