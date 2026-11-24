'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path');
const {signature}=require('./five-private.cjs'),{check}=require('./full-private.cjs');
const raw=Array.from({length:13},(_,i)=>[1<<i]);
const min=ts=>[...new Set(ts)].sort((a,b)=>a-b).filter((m,i,x)=>!x.slice(0,i).some(n=>(n&m)===n));
const minima=Array(13).fill(100);let checked=0;
for(const y of [1,2]){
  const a=[1,1<<y],terms=[...raw,a,...raw.map(([v])=>min(a.map(w=>w|v)))];
  const arms=[...new Map(terms.map(t=>[t.toString(),t])).values()];
  for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
    const g=min([...arms[i],...arms[j]]),key=g.toString();
    if([a,arms[i],arms[j]].some(w=>w.toString()===key))continue;
    checked++;
    const values=check([signature(a),signature(g)],0,8,true).sort((a,b)=>a-b);
    let sum=0;for(let k=0;k<13;k++){sum+=values[k];minima[k]=Math.min(minima[k],sum);}
  }
}
const b=require('../plane920-search/two-or-private.json');assert.equal(checked,b.count);assert.deepEqual(minima,b.low);
console.log(JSON.stringify({checked,minima}));

