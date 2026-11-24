const fs=require('node:fs'),path=require('node:path');
const {perm,apply}=require('../plane920-math/plane-orbits.js');
const {table,mult,join,raw,loc,lines,univ,pc,pm,orbits}=require('./three-or-five-lines.cjs');
const {priced}=require('./paid-or-arms.cjs');
const output=[];
for(const mask of [7,35]){
 const selected=lines.map((L,i)=>({L,i})).filter(x=>mask&1<<x.i);
 const ls=selected.map(x=>x.L),group=perm.filter(p=>ls.every(L=>ls.includes(apply(L,p))));
 const monos=[...new Set(ls.flatMap(L=>{const out=[];for(let m=L;m;m=(m-1)&L)out.push(m);return out;}))];
 const pos=t=>selected.reduce((m,{i,L})=>m|(t.some(x=>(x&L)===x)?1<<i:0),0);
 const inc=(m,n)=>(m|n)!==m&&(m|n)!==n;
 const first=new Map();
 for(const a of monos)for(const b of monos)if(a<b&&pc[a]<=2&&pc[b]<=2&&inc(pos([a]),pos([b])))first.set(a+','+b,[a,b]);
 const representatives=orbits(first,group),stats={mask,firsts:first.size,orbits:representatives.length,total:0,initialPass:0,tested:0,live:[]};
 for(const {t:firstOr} of representatives){
   const f=table(firstOr),firstMasks=firstOr.filter(m=>pc[m]>1).map(m=>[m]);
   const pool=new Map();
   for(const m of [0,...monos])for(const use of [false,true]){
     if(!m&&!use)continue;const t=use?mult([m],firstOr):[m],sign=pos(t);
     if(!sign)continue;pool.set(t.join(','),{t,w:table(t),sign});
   }
   const arms=[...pool.values()];
   const tests=selected.map(({i,L})=>{
     const olds=(f&loc[i])?f:univ,choices=[];
     for(let m=L;m;m=(m-1)&L)if(pc[m]===3)choices.push((table([m])&olds)^loc[i]);
     for(const a of arms){
       a.good??={};a.good[i]=choices.reduce((v,b,j)=>v|(!(b&a.w)?1<<j:0),0);
     }
     return {i,ok:choices.some(x=>!x)};
   });
   const seen=new Set();
   for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
     const a=arms[i],b=arms[j];if(!inc(a.sign,b.sign))continue;stats.total++;
     if(!tests.every(({i,ok})=>ok||(((a.sign|b.sign)&1<<i)&&(a.good[i]&b.good[i]))))continue;
     const t=join(a.t,b.t),key=t.join(',');
     if(key===firstOr.join(','))continue;
     const forced=[...firstMasks];
     for(const arm of [a,b]){
       if(raw.includes(arm.w)||arm.w===f||forced.some(x=>table(x)===arm.w))continue;
       forced.push(arm.t);
     }
     if(![...firstOr,...a.t,...b.t].some(x=>pc[x]>1))continue;
     stats.initialPass++;
     const sig=key+'/'+forced.map(t=>t.join(',')).sort().join('/');
     if(seen.has(sig))continue;seen.add(sig);
     // Any surviving pair of targets requires four out of five auxiliaries.
     if(selected.some(({i})=>forced.filter(x=>!(pos(x)&(mask^(1<<i)))).length>=2))continue;
     stats.tested++;
     const report=priced([firstOr,t],forced,3,5,mask);
     if(report.found)stats.live.push({firstOr,t,a:a.t,b:b.t,forced,report});
   }
 }
 output.push(stats);
}
fs.writeFileSync(path.join(__dirname,'two-or-three-lines-all.json'),JSON.stringify(output)+'\n');
console.log(output.map(({live,...s})=>({...s,live:live.length})));
