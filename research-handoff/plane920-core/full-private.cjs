'use strict';
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,j)=>m|1<<((i+j)%13),0));
const rows=Array.from({length:8192},(_,i)=>i).filter(x=>x.toString(2).replaceAll('0','').length===4);
const words=Math.ceil(rows.length/32), loc=lines.map(l=>rows.indexOf(l));
const cache=new Map();
function table(sig){
  if(cache.has(sig.key))return cache.get(sig.key);
  const terms=sig.key.split(',').map(Number),v=new Uint32Array(words);
  rows.forEach((r,i)=>{if(terms.some(t=>(r&t)===t))v[i>>5]|=1<<(i&31);});
  cache.set(sig.key,v);return v;
}
const raw=Array.from({length:13},(_,i)=>table({key:String(1<<i)}));
function check(ors,shared,limit=8,allCosts=false){
  const ot=ors.map(table);
  const lineMasks=lines.map((l,i)=>ors.reduce((m,o,j)=>m|((o.active>>i&1)<<j),0));
  const tmp=new Map();
  function maximum(point,mask){
    const key=(point<<ors.length)|mask;
    if(tmp.has(key))return tmp.get(key);
    const v=raw[point].slice();
    for(let i=0;i<ors.length;i++)if(mask&(1<<i))for(let w=0;w<words;w++)v[w]&=ot[i][w];
    tmp.set(key,v);return v;
  }
  let priv=0;
  const costs=[];
  for(let l=0;l<13;l++){
    const opts=new Set();
    for(let m=0;m<13;m++)if(m!==l){
      const p=31-Math.clz32(lines[m]&lines[l]);
      opts.add(maximum(p,lineMasks[l]&lineMasks[m]));
    }
    for(let i=0;i<ors.length;i++)if(ors[i].active===(1<<l))opts.add(ot[i]);
    const pool=[...opts], goal=loc[l]>>5, bit=1<<(loc[l]&31);
    function iso(a,b,c){
      for(let w=0;w<words;w++)if((a[w]&b[w]&(c?c[w]:-1)&(w===goal?~bit:-1))!==0)return false;
      return true;
    }
    let cost=2;
    for(let i=0;i<pool.length&&cost>0;i++)
      for(let j=0;j<=i;j++)if(iso(pool[i],pool[j])){
        cost=0;break;
      }
    if(cost===2){
      search: for(let i=2;i<pool.length;i++)for(let j=1;j<i;j++)for(let k=0;k<j;k++)
        if(iso(pool[i],pool[j],pool[k])){cost=1;break search;}
    }
    priv+=cost;
    if(allCosts)costs.push(cost);
    else if(priv+shared>limit)return false;
  }
  return allCosts?costs:true;
}
module.exports={check};

