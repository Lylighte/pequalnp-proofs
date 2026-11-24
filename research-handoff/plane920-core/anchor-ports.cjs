'use strict';
const {signature}=require('./unrestricted-prefix.cjs');
const pts=Array.from({length:13},(_,i)=>i),full=8191;
const lines=pts.map(i=>[0,1,3,9].reduce((m,q)=>m|1<<((q+i)%13),0));
const pencil=pts.map(p=>lines.reduce((m,l,i)=>m|(((l>>p)&1)<<i),0));
const pop=new Uint8Array(8192);for(let i=1;i<=full;i++)pop[i]=pop[i&(i-1)]+1;
const maxAnchors=lines.flatMap(l=>pts.filter(p=>!(l&(1<<p))).map(p=>l|1<<p));
const raw=a=>a.length===1&&pop[a[0]]===1?31-Math.clz32(a[0]):-1;
const cache=new Map(), completed=new Map();
function possible(missing,remaining){
  let total=0,same=0,used=0;
  const active=[];
  for(const p of pts){
    const a=missing[p];if(!a)continue;
    total+=pop[a];same|=used&a;used|=a;active.push(p);
  }
  if(total<=5&&!same)return true;
  if(!remaining)return false;
  if(total>5+8*remaining)return false;
  if(active.length<=remaining)return true; // one future mixed OR per point
  const vals=active.map(p=>pop[missing[p]]).sort((a,b)=>b-a);
  if(vals.slice(2*remaining).reduce((a,b)=>a+b,0)>5)return false;
  const key=remaining+'|'+missing.join(',');
  if(cache.has(key))return cache.get(key);
  // Cover all the incidences of a mixed OR's raw input, or all but the
  // common line at each input of a pure OR. A pair with an already covered
  // point is dominated by the mixed choice and can be omitted.
  const options=[];
  for(const p of active){
    const a=missing[p];options.push([p,0,-1,0,pop[a]]);
    for(const q of active){
      if(q>=p)break;
      const b=missing[q],l=pencil[p]&pencil[q];
      if(!(a&~l)||!(b&~l))continue;
      options.push([p,a&l,q,b&l,pop[a&~l]+pop[b&~l]]);
    }
  }
  options.sort((a,b)=>b[4]-a[4]);
  let answer=false;
  for(const [p,a,q,b] of options){
    const beforeP=missing[p],beforeQ=q>=0?missing[q]:0;
    missing[p]=a;if(q>=0)missing[q]=b;
    const ok=possible(missing,remaining-1);
    missing[p]=beforeP;if(q>=0)missing[q]=beforeQ;
    if(ok){answer=true;break;}
  }
  if(cache.size>200000)cache.clear();
  cache.set(key,answer);return answer;
}
function explain(gs,ps){
  const reached=pts.map(()=>0),anchors=new Map(),known=new Set(pts.map(i=>String(1<<i)));
  for(let j=0;j<gs.length;j++){
    const pair=ps[j];
    for(let k=0;k<2;k++){
      const arm=pair[k],q=raw(arm);
      if(q>=0){
        for(let i=0;i<13;i++)if(lines[i]&(1<<q)){
          const triple=lines[i]&~(1<<q);
          if(!pair[1-k].some(t=>(t&triple)===t))reached[q]|=1<<i;
        }
      }else if(!known.has(String(arm))){
        const f=signature(arm),forced=arm.reduce((a,b)=>a&b,full);
        if(pop[f.active]<=1)return {ok:false,reason:'helper true on at most one line'};
        const p=pts.find(x=>(f.active&~pencil[x])===0);
        if(p!==undefined){
          const old=anchors.get(p);
          if(old&&old.key!==f.key)return {ok:false,reason:'two helpers in one pencil'};
          // All direct raw ANDs and all these pencil-supported helpers together
          // satisfy the same four-pencil restriction. A helper that fails to
          // imply its point cannot itself be the direct AND at that point.
          anchors.set(p,{key:f.key,active:forced&(1<<p)?f.active:0});
        }
      }
    }
    known.add(gs[j].toString());
  }
  const need=[...anchors.keys()].reduce((v,p)=>v|1<<p,0);
  const callKey=[ps.length,need,...reached,...pts.map(p=>anchors.get(p)?.active??-1)].join(',');
  if(completed.has(callKey))return {ok:completed.get(callKey)};
  if(completed.size>100000)completed.clear();
  for(const zone of maxAnchors){
    if((zone&need)!==need)continue;
    const missing=pts.map(p=>{
      const credit=anchors.get(p)?.active??((zone&(1<<p))?pencil[p]:0);
      return pencil[p]&~(reached[p]|credit);
    });
    if(possible(missing,8-ps.length)){completed.set(callKey,true);return {ok:true};}
  }
  completed.set(callKey,false);
  return {ok:false,reason:'uncovered point deletions'};
}
module.exports={explain,possible};
