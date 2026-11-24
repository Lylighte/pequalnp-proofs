const {goal}=require('./formula.cjs');
const assert=require('node:assert/strict');
function check(gates){
 const table=Array.from({length:128},(_,m)=>{
   const w=Array.from({length:7},(_,i)=>!!(m&(1<<i)));
   for(const [op,...is] of gates){
     const us=is.map(i=>w[i]??false);
     const z=op==='&'?us.every(Boolean):op==='|'?us.some(Boolean):!us[0];
     w.push(z);
   }
   return w;
 });
 const correct=table.every((r,m)=>r.at(-1)===goal(m));
 const elim=[];
 for(let p=0;p<7;p++)for(let b=0;b<2;b++){
   const subset=table.filter((r,m)=>Number(!!(m&(1<<p)))===b);
   const seen=new Set([0n,(1n<<64n)-1n]),g=[];
   for(let w=0;w<table[0].length;w++){
     const col=subset.reduce((s,r,i)=>s+(r[w]?1n<<BigInt(i):0n),0n);
     if(w>=7&&seen.has(col))g.push(w-7);
     seen.add(col);
   }
   elim.push(g);
 }
 return {correct,elim,tight:elim.map((g,i)=>g.length>=(i%2?4:3))};
}
module.exports={check};
