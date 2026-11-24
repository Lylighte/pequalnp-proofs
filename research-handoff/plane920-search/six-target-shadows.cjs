const fs=require('node:fs'),path=require('node:path');
const {families,prefixes}=require('./five-or-six-targets.cjs'),{lines,pc}=require('./three-or-five-lines.cjs');
const nibble=new Uint8Array(64),fullPos=new Uint32Array(64),cost=new Uint8Array(4096);
for(let m=0;m<64;m++)for(let j=0;j<6;j++)if(m&1<<j)fullPos[m]|=15<<(4*j);
for(let m=0;m<4096;m++)for(let j=0;j<3;j++)cost[m]+=Math.max(0,2-pc[(m>>>(4*j))&15]);
function env(M){
 const sel=lines.filter((L,i)=>M&1<<i),rows=[];
 for(const L of sel)for(let p=0;p<13;p++)if(L&1<<p)rows.push(L^(1<<p));rows.push(...sel);
 const truth=t=>rows.reduce((w,x,i)=>w|(t.some(s=>(s&x)===s)?1<<i:0),0);
 const raw=Array.from({length:13},(_,p)=>truth([1<<p]));
 function pool(prev){
  const terms=[0x3fffffff];for(const w of prev){const n=terms.length;for(let i=0;i<n;i++)terms.push(terms[i]&w);}
  const set=new Set();
  for(const r of [0x3fffffff,...raw])for(const t of terms){const v=t&r;if(v!==0x3fffffff&&pc[v>>>24]>=2)set.add(v);}
  return [...set];
 }
 const bits=v=>fullPos[v>>>24]&~v;
 const price=k=>cost[k&4095]+cost[k>>>12];
 function outs(prev){
   const arms=pool(prev),ps=arms.map(n=>n>>>24),vs=new Set();
   for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++)if(pc[ps[i]&~ps[j]]>=2&&pc[ps[j]&~ps[i]]>=2)vs.add(arms[i]|arms[j]);
   return vs;
 }
 return {truth,raw,outs,pool,bits,price};
}
if(require.main===module){
 const lim=Number(process.argv[2]||1000000),start=Date.now(),out=[];
 for(const {m,gp} of families){
  const {truth,outs,bits,price}=env(m),seen=new Set(),stats={m,three:0,four:0,late:0,pass:0,passFour:0};
  prefixes(m,gp,3,(t,g)=>{
   if(stats.three++>=lim)return;const prev=t.map(truth),base=prev.reduce((k,v)=>k|bits(v),0);
   for(const q of outs(prev)){
     const four=[...prev,q].sort((a,b)=>a-b),key=four.join(',');if(seen.has(key))continue;seen.add(key);stats.four++;
     const initial=base|bits(q);let pass=false;
     for(const v of outs(four)){stats.late++;if(price(initial|bits(v))<=2){stats.pass++;pass=true;}}
     if(pass)stats.passFour++;
   }
  });out.push(stats);console.log(stats);
 }
 fs.writeFileSync(path.join(__dirname,'six-target-shadows-'+lim+'.json'),JSON.stringify({out,ms:Date.now()-start})+'\n');
}
module.exports={env};
