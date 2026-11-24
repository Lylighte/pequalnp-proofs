'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {prefixes}=require('./three-prefix-all.cjs');
const {bounds}=require('./early-fold.cjs'),{signature}=require('./unrestricted-prefix.cjs');
const d=path.join(__dirname,'unrestricted');
const load=prefix=>fs.readdirSync(d).filter(f=>f.startsWith(prefix)).flatMap(f=>fs.readFileSync(path.join(d,f),'utf8').trim().split('\n').filter(Boolean).map(JSON.parse));
const fourth=load('early-four-29-67-'),fifth=load('early-five-29-6-');
const ids=fourth.map(r=>r.id).sort((a,b)=>a-b);
assert.deepEqual(ids,Array.from({length:3370},(_,i)=>i));
const want=fourth.flatMap(r=>r.live.filter(x=>x[3].includes(6)).map(x=>[r.id,x[0],x[1]].join(','))).sort();
const got=fifth.map(r=>[r.id,r.i,r.j].join(',')).sort();
assert.deepEqual(got,want);assert.equal(new Set(got).size,got.length);
// Directly check all subfamilies rather than optimizing by private multiplicity.
const pop=x=>x.toString(2).replaceAll('0','').length;
const min=(n,e)=>{
  const free=[0,2,4,5,5,6,6,6,6,7,7,7,7,7][n];
  if(e<=1)return 2*n;
  if(e===2)return Math.max(free,[0,2,4,5,7,9,11][Math.min(n,6)]);
  if(e===3)return Math.max(free,[0,2,4,5,6,8,10][Math.min(n,6)]);
  if(e===4)return Math.max(free,[0,2,4,5,5,8,9][Math.min(n,6)]);
  return free;
};
function exhaustive(gs,ps,h){
  let lower=7;const prior=new Set(Array.from({length:13},(_,i)=>String(1<<i))),paid=new Map();
  const final=new Map();
  for(let j=0;j<ps.length;j++){
    for(const arm of ps[j])if(!prior.has(String(arm))){
      const {active,key}=signature(arm);paid.set(key,active);
      const single=arm.filter(a=>pop(a)===1).reduce((m,z)=>m|signature([z]).active,0);
      final.set(key,active&~single);
    }
    prior.add(String(gs[j]));
    for(let v=0;v<(1<<(j+1));v++){
      let s=8191;
      for(let a=0;a<=j;a++){
        const pair=ps[a].map(q=>signature(q).active),keep=(v>>a)&1;
        s&=~(pair[1-keep]&~pair[keep]);
      }
      for(let t=s;t;t=(t-1)&s){
        const removed=[...paid.values()].filter(m=>pop(m&s)>1||!(m&t)).length;
        lower=Math.max(lower,removed+min(pop(t),h-j-1));
      }
    }
  }
  const z=[...final.values()];
  for(let b=1;b<(1<<z.length);b++){
    let s=8191;z.forEach((m,i)=>{if(b&(1<<i))s&=~m;});
    lower=Math.max(lower,pop(b)+min(pop(s),10));
  }
  return lower;
}
let checks=0;
const {getArms,join}=require('./unrestricted-prefix.cjs');
for(const id of [0,18,59,501,1001,1807,2274,3130,3369]){
  const {gs,ps}=prefixes[id],h=7;
  assert.equal(bounds(gs,ps,[h])[h],exhaustive(gs,ps,h));checks++;
}
for(const r of fifth.filter((_,i)=>i%17===0)){
  const {gs,ps}=prefixes[r.id],arms=getArms(gs),pair=[arms[r.i],arms[r.j]],xs=[...gs,join(...pair)],ys=[...ps,pair];
  for(const h of [6,7]){assert.equal(bounds(xs,ys,[h])[h],exhaustive(xs,ys,h));checks++;}
}
const sum=(arr,f)=>arr.reduce((n,r)=>n+f(r),0);
const result={three:ids.length,fourRoots:sum(fourth,r=>Number(r.eligible.length>0)),four:sum(fourth,r=>r.orbits),fourFold:sum(fourth,r=>r.counts[6].fold),fourLive:want.length,five:sum(fifth,r=>r.orbits),fiveLabelled:sum(fifth,r=>r.labelled),fiveFold:sum(fifth,r=>r.fold),fiveLive:sum(fifth,r=>r.live.length),caps:sum(fourth,r=>r.counts[6].capped)+sum(fifth,r=>r.capped),directComparisons:checks};
assert.equal(result.fiveLive,0);assert.equal(result.caps,0);
fs.writeFileSync(path.join(d,'early-29-h6-audit.json'),JSON.stringify(result)+'\n');console.log(result);
