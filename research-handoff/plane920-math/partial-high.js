"use strict";
const fs=require("node:fs"),path=require("node:path");
const {lines,weight:w,perm,apply}=require("./plane-orbits");
const pts=Array.from({length:13},(_,i)=>i),full=8191,s=Number(process.argv[2]||4095),n=w[s];
const allmaps=perm.map(p=>lines.map(l=>lines.indexOf(apply(l,p)))),maps=allmaps.filter(p=>apply(s,p)===s);
const privateRows=Array.from({length:8192},(_,r)=>pts.reduce((m,i)=>{
 if(!(r&(1<<i)))return m;let a=lines[i];for(const j of pts)if(j!==i&&(r&(1<<j)))a&=~lines[j];return a?m|(1<<i):m;},0));
const orbitA=new Set(),recs=[];
function whereMiss(a){const t=s^a,k=w[t];if(k>=6)return 0;if(k===5)return t;return s;}
const twoRaw=(a,b)=>privateRows[a]|privateRows[b];
for(let a=0;a<=full;a++){
 if((a&~s)||orbitA.has(a)||w[privateRows[a]]<3)continue;
 const aut=[],oa=new Set();for(const p of maps){const g=apply(a,p);oa.add(g);if(g===a)aut.push(p);}
 for(const c of oa)orbitA.add(c);
 const orbitB=new Set();
 for(let b=0;b<=full;b++){
  if((b&~s)||orbitB.has(b)||w[s&~(a|b)]>2||w[privateRows[b]]<3||w[privateRows[b]]>w[privateRows[a]])continue;
  const ob=new Set(aut.map(p=>apply(b,p)));for(const c of ob)orbitB.add(c);
  const hh=w[a&b]===1?a&b:0,lowOrA=whereMiss(b)&a,lowOrB=whereMiss(a)&b,lowPair=whereMiss(a)&whereMiss(b);
  const possible=hh|lowOrA|lowOrB|lowPair,raw=twoRaw(a,b),uncovered=s&~raw;
  // After both highs have three target lines, they occupy slots 5 and 6. The first
  // three lows cannot be a raw partner, and a fourth low cannot if either high
  // covers too few rows to unite with a four-line pencil to reach n-2.
  const lowCap=(Math.min(w[a],w[b])+4>=n-2)?1:0;
  if(w[uncovered&~possible]>lowCap||w[uncovered]>lowCap+Math.min(4,w[uncovered&possible]))continue;
  recs.push({a,b,raw,lowCap,hh,lowOrA,lowOrB,lowPair,orbit:oa.size*ob.size});
 }
}
const counts={};for(const r of recs){const k=[w[r.a],w[r.b],r.lowCap].join("-");counts[k]=(counts[k]||0)+1;}
const fn=path.join(__dirname,"small-core","partial-high-"+s+".json");fs.writeFileSync(fn,JSON.stringify({s,n,counts,recs},null,2)+"\n");
console.log({s,n,maps:maps.length,reps:recs.length,labeled:recs.reduce((a,r)=>a+r.orbit,0),counts});
