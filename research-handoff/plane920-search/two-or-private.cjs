const fs=require('node:fs'),path=require('node:path');
const {inspect}=require('./private-independent.cjs');
const pop=m=>m.toString(2).replaceAll('0','').length;
const all=Array.from({length:8192},(_,m)=>m).filter(m=>pop(m)<=4);
const raw=Array.from({length:13},(_,p)=>all.reduce((w,m,j)=>w|((m&1<<p)?1n<<BigInt(j):0n),0n));
const low=Array(14).fill(Infinity),hist={},examples={},start=Date.now();let count=0;
const firstRoots=[[0,1],[0,2]];
for(const [a,b] of firstRoots){
 const first=raw[a]|raw[b],arms=[...new Set([...raw,first,...raw.map(r=>r&first)])];
 for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
   const out=arms[i]|arms[j];if(out===arms[i]||out===arms[j]||out===first)continue;
   const {costs}=inspect([first,out],100),ordered=costs.slice().sort((x,y)=>x-y);
   let c=0;for(let k=1;k<=13;k++){
     c+=ordered[k-1];if(c<low[k]){low[k]=c;examples[k]={a,b,i,j,costs};}
   }
   const c6=ordered.slice(0,6).reduce((x,y)=>x+y);hist[c6]=(hist[c6]||0)+1;count++;
 }
}
const analytic=low.map((m,i)=>Math.min(m,Math.max(0,2*i-3)));
const summary={count,low:low.slice(1),minimumWithMultiArm:analytic.slice(1),hist,examples,ms:Date.now()-start};
fs.writeFileSync(path.join(__dirname,'two-or-private.json'),JSON.stringify(summary)+'\n');console.log(summary.low,summary.minimumWithMultiArm,hist);
