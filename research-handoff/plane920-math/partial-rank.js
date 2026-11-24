"use strict";
const fs=require("node:fs"),path=require("node:path");
const {lines,weight:w,perm,apply}=require("./plane-orbits");
const pts=Array.from({length:13},(_,i)=>i),full=8191,s=Number(process.argv[2]||2047),n=w[s],allmaps=perm.map(p=>lines.map(l=>lines.indexOf(apply(l,p)))),maps=allmaps.filter(p=>apply(s,p)===s);
const pr=Array.from({length:8192},(_,r)=>pts.reduce((m,i)=>{if(!(r&(1<<i)))return m;
 let a=lines[i];for(const j of pts)if(j!==i&&(r&(1<<j)))a&=~lines[j];return a?m|(1<<i):m;},0));
function whereMiss(a){const t=s^a,k=w[t];if(k>=6)return 0;if(k===5)return t;return s;}
const seenA=new Set(),recs=[];
for(let a=0;a<=full;a++){
 if((a&~s)||seenA.has(a)||w[pr[a]]<3)continue;
 const aut=[],oa=new Set();for(const p of maps){const g=apply(a,p);oa.add(g);if(g===a)aut.push(p);}for(const u of oa)seenA.add(u);
 const seenB=new Set();
 // b=-1 denotes a one-high placement.
 for(let b=-1;b<=full;b++){
  if(b>=0&&((b&~s)||seenB.has(b)||w[s&~(a|b)]>2))continue;
  const ob=b<0?new Set([-1]):new Set(aut.map(p=>apply(b,p)));for(const u of ob)seenB.add(u);
  for(const hA of [4,5])for(const hB of (b<0?[-1]:[2,3,4,5].filter(x=>x!==hA))){
   if(b>=0&&(b===a&&hA>hB))continue;
   const available=[3,4,5].filter(g=>g!==hA&&g!==hB&&(g!==3||4+Math.min(w[a],b<0?99:w[b])>=n-2));
   const Bcap=b<0?0:[0,0,1,2,6,6][hB];
   const pa=pr[a],pb=b<0?0:pr[b];
   const hh=b>=0&&w[a&b]===1?a&b:0,
      lowA=b<0?a:(whereMiss(b)&a),lowB=b<0?0:(whereMiss(a)&b),
      ll=b<0?whereMiss(a):(whereMiss(a)&whereMiss(b)),possible=hh|lowA|lowB|ll;
   const mustRaw=s&~possible;
   if(w[mustRaw&~(pa|pb)]>available.length||w[mustRaw&~pa]>available.length+Bcap)continue;
   // Necessary assignment over disjoint raw-high A, raw-high B, generic raw-low,
   // and helper pairs. Iterate the small choice of up to six high-B raw rows.
   let ok=false;
   for(let chosen=pb;;chosen=(chosen-1)&pb){
    if(w[chosen]<=Bcap){
     const paUse=pa&~chosen;if(w[paUse]>=3){
      const left=s&~(chosen|paUse);
      if(w[left&~possible]<=available.length&&w[left]<=available.length+Math.min(4,w[left&possible])){ok=true;break;}
     }
    }
    if(!chosen)break;
   }
   if(ok)recs.push({a,b,hA,hB,available,hh,lowA,lowB,ll,orbit:oa.size*ob.size});
  }
 }
}
const types={};for(const r of recs){const k=[r.hA,r.hB,w[r.a],r.b<0?-1:w[r.b]].join("-");types[k]=(types[k]||0)+1;}
const fn=path.join(__dirname,"small-core","partial-rank-"+s+".json");fs.writeFileSync(fn,JSON.stringify({s,n,types,recs},null,2)+"\n");console.log({s,n,group:maps.length,recs:recs.length,types});
