const fs=require('node:fs'),path=require('node:path');
const {roots,terms}=require('./bounded-three-or.cjs'),{table,raw}=require('./three-or-five-lines.cjs');
const {paidFor}=require('./two-tight-kernel.cjs'),{priced}=require('./paid-or-arms.cjs');
const out=[];
for(const k of [4,5])for(const q of require('./two-tight-kernel-'+k+'-4024.json').live){
 const gs=roots[q.j],{paid,cuts}=paidFor(gs,q.ps),H=q.ps[1][0],h=table(H),named=new Set([...raw,table(gs[0])]);
 const pool=terms([gs[0]]).map(({t})=>[t,table(t)]).filter(([t,w])=>w!==h);
 const already=new Set(paid.map(table)),tries=[];
 for(let i=0;i<pool.length;i++)for(let j=0;j<i;j++){
  const [a,w]=pool[i],[b,v]=pool[j];if((w&v)!==h)continue;
  const extra=[[a,w],[b,v]].filter(([t,z])=>!named.has(z)&&!already.has(z)).map(([t])=>t);
  const r=priced(gs,[...paid,...extra],k,2*k-1,0,1,cuts);
  tries.push({a,b,r});
 }
 out.push({k,j:q.j,tries});
}
fs.writeFileSync(path.join(__dirname,'two-tight-expanded.json'),JSON.stringify(out)+'\n');
console.log(out.map(x=>({k:x.k,tested:x.tries.length,live:x.tries.filter(t=>t.r.found).length})));
