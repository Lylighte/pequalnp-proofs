'use strict';
const {signature, fixed}=require('./unrestricted-prefix.cjs'),{check}=require('./full-private.cjs');
const full=8191,pc=new Uint8Array(8192);
for(let s=1;s<=full;s++)pc[s]=pc[s&(s-1)]+1;
const lines=Array.from({length:13},(_,j)=>[0,1,3,9].reduce((m,v)=>m|1<<((v+j)%13),0));
const stars=lines.map((_,i)=>lines.reduce((m,l,j)=>m|((l>>i&1)<<j),0));
const syms=[0,full,...stars,...lines.map((_,i)=>1<<i)];
function baseAnd(n,e){
  if(e<=1)return 2*n;
  let v=[0,2,4,5][Math.min(n,3)];
  if(e<=2){if(n>=4)v=7;if(n>=5)v=9;if(n>=6)v=11;}
  if(e<=3){if(n>=4)v=Math.max(v,6);if(n>=5)v=Math.max(v,8);if(n>=6)v=Math.max(v,10);}
  if(e<=4&&n>=5)v=Math.max(v,7);
  if(n>=12)v=Math.max(v,7);
  return v;
}
function prepare(gs,ps,hidden,strong=false){
  const os=gs.map(signature),costs=check(os,0,0,true),f=fixed(gs,ps);
  const arms=ps.map(p=>p.map(signature));
  const known=new Set(lines.map((_,i)=>(1<<i).toString())),due=new Map();
  for(let j=0;j<gs.length;j++){
    for(const a of arms[j])if(!known.has(a.key))due.set(a.key,a.active);
    known.add(os[j].key);
  }
  const spare=[...due.values()].filter(x=>pc[x]!==1);
  const base=f.priv.reduce((a,b)=>a+b,0);
  const deltas=costs.map((c,i)=>Math.max(0,c-f.priv[i]));
  const d1=deltas.reduce((m,v,i)=>m|((v>=1?1:0)<<i),0),d2=deltas.reduce((m,v,i)=>m|((v>=2?1:0)<<i),0);
  const value=s=>pc[s&d1]+pc[s&d2];
  const cache=new Int8Array(8192),feas=new Int8Array(8192),maxK=hidden-f.shared-base;
  const charge=costs.map((c,i)=>Math.max(c,f.priv[i]));
  function lower(t){
    if(cache[t])return cache[t]-40;
    const e=arms.filter(([a,b])=>(t&a.active&~b.active)&&(t&b.active&~a.active)).length;
    const absent=spare.filter(m=>!(m&t)).length;
    let inside=0;for(let s=t;s;s&=s-1)inside+=charge[31-Math.clz32(s&-s)];
    const n=pc[t];
    let small=baseAnd(n,e);
    if(strong){
      if(n>=5&&e<=4)small=Math.max(small,8);
      if(n>=6&&e<=4)small=Math.max(small,9);
      if(n>=6)small=Math.max(small,6);
      if(n>=10)small=Math.max(small,7);
    }
    const v=small+absent-inside;cache[t]=40+v;return v;
  }
  function fits(s){
    if(feas[s])return feas[s]===1;
    const w=base+value(s);
    if(w+f.shared>hidden){feas[s]=-1;return false;}
    if(!f.shared&&w===hidden&&pc[s]*2>hidden){feas[s]=-1;return false;}
    for(let t=s;t;t=(t-1)&s)if(w+lower(t)>hidden){feas[s]=-1;return false;}
    feas[s]=1;return true;
  }
  const products=new Set(syms);
  for(const o of os)for(const r of [...products])products.add(r&o.active);
  const domain=[...products].filter(r=>r&&r!==full);
  return {os,domain,value,maxK,fits};
}
function search(gs,ps,hidden,depth,cap=800000,strong=false){
  const {domain,value,maxK,fits}=prepare(gs,ps,hidden,strong);
  const memo=new Map();
  function adaptive(s,d){
    if(fits(s))return true;if(!d||value(s)>maxK*(1<<d))return false;
    const key=s*8+d;if(memo.has(key))return memo.get(key);
    let ok=adaptive(s,d-1);
    if(!ok){
      const possible=domain.filter(a=>adaptive(s&~a,d-1));
      for(let i=1;i<possible.length&&!ok;i++)for(let j=0;j<i;j++){
        const a=possible[i],b=possible[j];
        if(adaptive(s&(~a|b),d-1)&&adaptive(s&(~b|a),d-1)){ok=true;break;}
      }
    }
    memo.set(key,ok);return ok;
  }
  let visited=0;
  function fixedGame(sets,dom,d){
    const ss=[...new Set(sets)].filter(s=>!fits(s)).sort((a,b)=>pc[b]-pc[a]);
    const essential=ss.filter((s,i)=>!ss.slice(0,i).some(t=>(s&t)===s));
    if(!essential.length)return true;
    if(!d)return false;
    if(++visited>cap)return true;
    if(!essential.every(s=>adaptive(s,d)))return false;
    const arms=dom.filter(a=>essential.every(s=>adaptive(s&~a,d-1)));
    for(let i=1;i<arms.length;i++)for(let j=0;j<i;j++){
      const a=arms[i],b=arms[j],x=a&~b,y=b&~a;
      if(!x||!y)continue;
      const next=[];let pass=true;
      for(const m of essential){
        const l=m&~x,r=m&~y;
        if(!adaptive(l,d-1)||!adaptive(r,d-1)){pass=false;break;}
        next.push(l,r);
      }
      if(!pass)continue;
      if(d===1)return true;
      const u=a|b,newdom=new Set([u,...dom]);for(const z of dom)if(z&u)newdom.add(z&u);
      if(fixedGame(next,[...newdom],d-1))return true;
    }
    return false;
  }
  return {open:fixedGame([full],domain,depth),visited,capped:visited>cap};
}
module.exports={baseAnd,prepare,search};

