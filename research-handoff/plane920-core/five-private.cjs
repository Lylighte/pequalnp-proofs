'use strict';
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,j)=>m|(1<<((i+j)%13)),0));
const pts=lines.map(l=>Array.from({length:13},(_,i)=>i).filter(i=>l&(1<<i)));
const index=new Map();
function signature(terms) {
  const key=terms.join(',');
  if(index.has(key))return index.get(key);
  const sensitive=[], common=[];
  let active=0;
  for(let i=0;i<13;i++) {
    const hits=terms.filter(t=>(t&lines[i])===t);
    if(!hits.length){sensitive.push(0);common.push(0);continue;}
    active|=1<<i;
    const need=hits.reduce((a,b)=>a&b,lines[i]);
    sensitive.push(pts[i].reduce((z,p,n)=>z|((need>>p&1)<<n),0));common.push(need);
  }
  const ans={key,active,sensitive,common};index.set(key,ans);return ans;
}
const raw=Array.from({length:13},(_,i)=>signature([1<<i]));
const meetBit=lines.map((l,i)=>lines.map((r,j)=>i===j?0:1<<pts[i].indexOf(31-Math.clz32(l&r))));
const pc=Array.from({length:16},(_,i)=>i.toString(2).replaceAll('0','').length);
const price=new Uint8Array(65536);
for(let available=0;available<65536;available++){
  let one=false,two=false,three=false;
  for(let a=1;a<16;a++)if(available&(1<<a)){
    if(a===15)one=true;
    for(let b=1;b<16;b++)if(available&(1<<b)){
      const ab=a|b;
      if(ab===15)two=true;
      if(pc[ab]>=3)three=true;
    }
  }
  price[available]=one||two?0:three?1:2;
}
function bound(ors,operands){
  // Remove any OR one of whose arms can be discarded on every positive row.
  if(operands.some(([a,b])=>!(a.active&~b.active)||!(b.active&~a.active)))return {reason:'dominated'};
  const earlier=new Set(raw.map(q=>q.key)), forced=new Set();
  for(let i=0;i<5;i++){
    for(const a of operands[i])if(!earlier.has(a.key)&&(a.active&(a.active-1)))forced.add(a.key);
    earlier.add(ors[i].key);
  }
  // The indispensable surplus AND accepts at least four lines. If all forced
  // shared arms accept fewer than four, that gate is distinct from each.
  const shared=forced.size+Number(!operands.flat().some(a=>forced.has(a.key)&&
    (a.active.toString(2).replaceAll('0','').length>=4)));
  let privateTotal=0;
  for(let l=0;l<13;l++){
    let options=(1<<1)|(1<<2)|(1<<4)|(1<<8);
    for(const o of ors)if(o.active&(1<<l)) options|=1<<o.sensitive[l];
    for(let m=0;m<13;m++)if(m!==l){
      let sensitive=meetBit[l][m];
      for(const o of ors)if((o.active&(1<<l))&&(o.active&(1<<m)))sensitive|=o.sensitive[l];
      options|=1<<sensitive;
    }
    privateTotal+=price[options];
  }
  return {reason:privateTotal+shared>8?'budget':'survives',privateTotal,shared};
}
module.exports={bound,signature};

