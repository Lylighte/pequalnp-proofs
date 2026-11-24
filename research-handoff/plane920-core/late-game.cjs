'use strict';
const all=8191;
const size=new Uint8Array(8192);
for(let s=1;s<=all;s++)size[s]=1+size[s&(s-1)];
const lines=Array.from({length:13},(_,j)=>[0,1,3,9].reduce((m,v)=>m|1<<((v+j)%13),0));
const pencils=lines.map((_,i)=>lines.reduce((m,l,j)=>m|((l>>i&1)<<j),0));
function terminalGame(gates,costs,hidden,depth,forced=0,privateFloor=[],strict=true){
  const bound=hidden-forced;
  const prods=[all];
  for(const g of gates){const tmp=prods.slice();for(const t of tmp)prods.push(t&g.active);}
  const signatures=new Set([0,all,...pencils,...lines.map((_,i)=>1<<i)]);
  for(const v of prods){signatures.add(v);for(const p of pencils)signatures.add(v&p);}
  const sig=[...signatures].filter(s=>s!==all&&s!==0);
  let one=0,two=0,base=0;
  for(let i=0;i<13;i++){
    const f=privateFloor[i]||0; base+=f;
    const delta=Math.max(0,costs[i]-f);
    if(delta)one|=1<<i;if(delta===2)two|=1<<i;
  }
  const value=s=>size[s&one]+size[s&two],limit=bound-base;
  const memo=new Map();
  function familyFits(s,w){
    const charges=[];
    for(let i=0;i<13;i++)if(s&(1<<i))charges.push(Math.max(costs[i],privateFloor[i]||0));
    charges.sort((a,b)=>a-b);
    let reusable=0;
    for(let r=1;r<=Math.min(3,charges.length);r++){
      reusable+=charges[r-1];
      if(w+base-reusable+[0,2,4,5][r]>hidden)return false;
    }
    return true;
  }
  function weak(s,d){
    const w=value(s);
    // In the tie every counted gate is physical. If none is allowed to be
    // shared, each surviving target needs two active private ANDs.
    const tie= strict && forced===0 && w===limit && 2*size[s]>hidden;
    if((w<limit||(w===limit&&!tie))&&familyFits(s,w))return true;
    if(!d||w>limit*(1<<d))return false;
    const key=s*8+d;
    if(memo.has(key))return memo.get(key);
    const threshold=Math.max(0,w-limit*(1<<(d-1)));
    const candidates=sig.filter(a=>value(a&s)>=threshold);
    for(let i=1;i<candidates.length;i++)for(let j=0;j<i;j++){
      const a=candidates[i],b=candidates[j],x=s&a&~b,y=s&b&~a;
      if(!x||!y||value(x)<threshold||value(y)<threshold)continue;
      if(weak(s^x,d-1)&&weak(s^y,d-1)){memo.set(key,true);return true;}
    }
    // An uninformative OR can be removed; for d>=2 allow a shorter strategy.
    const result=d>1&&weak(s,d-1);memo.set(key,result);return result;
  }
  return weak(all,depth);
}
module.exports={terminalGame};

