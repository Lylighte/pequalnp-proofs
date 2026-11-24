"use strict";
const fs=require("node:fs"),path=require("node:path"),{lines,weight:w,perm,apply}=require("./plane-orbits");
const pts=Array.from({length:13},(_,i)=>i),ids=m=>pts.filter(i=>m>>i&1),full=8191;
const lm=perm.map(p=>lines.map(l=>lines.indexOf(apply(l,p)))),seen=new Set(),recs=[];
for(let S=0;S<=full;S++)if(w[S]===5&&!seen.has(S)){
 const aut=[];for(const g of lm){const t=apply(S,g);seen.add(t);if(t===S)aut.push(g);}
 const h=ids(S),loc=r=>h.reduce((m,x,i)=>m|((r>>x&1)<<i),0);
 const P=pts.map(p=>loc(lines.reduce((m,l,i)=>m|(((l>>p)&1)<<i),0)));
 const masks=Array.from({length:32},(_,i)=>i).filter(x=>w[x]>=3);
 const pr=m=>P.reduce((b,p)=>w[p&m]===1?b|(p&m):b,0);
 const raw4=m=>P.some(p=>(p&m)===m);
 const R=[],packs=[],stat={};let total=0;
 function scan(k){
  if(k<5){for(const m of masks)if(R.every(r=>w[31&~(m|r)]<=1)){R.push(m);scan(k+1);R.pop();}return;}
  let paired=0;
  for(let i=0;i<5;i++)for(let j=0;j<i;j++)if(i!==1&&w[R[i]&R[j]]===1)paired|=R[i]&R[j];
  const rem=31^paired;if(!rem){packs.push([...R]);return;}
  const m4=raw4(R[3])?pr(R[3]):0,m5=pr(R[4]),n5=raw4(R[4])?4:1;
  const k4=[0,...Array.from({length:5},(_,i)=>1<<i).filter(b=>b&m4)];
  if(!k4.some(q=>(rem&~q&~m5)===0&&w[rem&~q]<=n5))return;
  packs.push([...R]);
 }
 scan(0);
 const mapped=aut.map(g=>Array.from({length:32},(_,m)=>h.reduce((a,b,i)=>a|((m>>i&1)<<h.indexOf(g[b])),0)));
 const done=new Set(),uniq=[];for(const row of packs){const key=row.join("-");if(done.has(key))continue;uniq.push(row);for(const p of mapped)done.add(row.map(r=>p[r]).join("-"));}
 for(const z of uniq){const co=z.map(r=>w[r]).join("");stat[co]=(stat[co]||0)+1;}
 recs.push({S,total:packs.length,uniq:uniq.length,rows:uniq,stat});console.log(S,packs.length,uniq.length);
}
fs.writeFileSync(path.join(__dirname,"small-core","five-target-signatures.json"),JSON.stringify(recs)+"\n");
