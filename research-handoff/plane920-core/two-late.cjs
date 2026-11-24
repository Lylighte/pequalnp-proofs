'use strict';
// Earlier OR functions stay fixed. Resolve both later ORs toward one child.
// After either choice, every future operand is a conjunction of raw variables
// and the five fixed ORs. Only these signatures on the thirteen positives matter.
const full=8191;
const stars=Array.from({length:13},(_,p)=>Array.from({length:13},(_,l)=>[0,1,3,9].some(v=>(v+l)%13===p)?1<<l:0).reduce((a,b)=>a|b));
const raw=[0,full,...stars,...stars.map((_,i)=>1<<i)];
const pc=new Uint8Array(8192);
for(let s=1;s<=full;s++)pc[s]=1+pc[s&(s-1)];
function failure(ors,costs,limit){
  let once=0,twice=0;
  costs.forEach((c,i)=>{if(c)once|=1<<i;if(c===2)twice|=1<<i;});
  const value=m=>pc[m&once]+pc[m&twice];
  const total=value(full), rootThreshold=total-2*limit;
  const groups=[full];
  for(const o of ors){const old=groups.slice();for(const g of old)groups.push(g&o.active);}
  const sig=[...new Set(groups.flatMap(g=>raw.map(r=>r&g)))];
  const root=sig.filter(a=>value(a)>=rootThreshold);
  const cache=new Map();
  function weak(s){
    if(cache.has(s))return cache.get(s);
    const cost=value(s),t=cost-limit;
    if(cost>2*limit)return false;
    if(cost<=limit)return true;
    const arms=sig.filter(a=>value(a&s)>=t);
    for(let i=1;i<arms.length;i++)for(let j=0;j<i;j++){
      const a=arms[i],b=arms[j];
      if(value(s&a&~b)>=t && value(s&b&~a)>=t){
        cache.set(s,true);return true;
      }
    }
    cache.set(s,false);return false;
  }
  for(let i=1;i<root.length;i++)for(let j=0;j<i;j++){
    const a=root[i],b=root[j],x=a&~b,y=b&~a;
    if(value(x)>=rootThreshold&&value(y)>=rootThreshold&&weak(full^x)&&weak(full^y))
      return [a,b,full^x,full^y];
  }
  return null;
}
module.exports={failure};

