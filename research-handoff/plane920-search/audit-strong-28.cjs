const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {table,pm,pc,raw,loc,lines}=require('./three-or-five-lines.cjs'),{inspect}=require('./private-independent.cjs');
const {prepare}=require('../plane920-core/effective-cut.cjs'),{restore}=require('../plane920-core/critical-next.cjs');
const dir=path.join(__dirname,'../plane920-core/unrestricted');
const read=kind=>fs.readdirSync(dir).filter(f=>f.startsWith(kind+'-')&&f.endsWith('-8000.jsonl')).flatMap(f=>fs.readFileSync(path.join(dir,f),'utf8').trim().split('\n').filter(Boolean).map(t=>JSON.parse(t)));
const fives=read('critical-fifth'),sixes=read('critical-level-6');
assert.equal(fives.length,1217);assert.deepEqual(fives.map(r=>r.id).sort((a,b)=>a-b),Array.from({length:1217},(_,i)=>i));
const key=(i,t)=>i+':'+t.join(',');
assert.deepEqual(sixes.map(r=>key(r.id,r.trail)).sort(),fives.flatMap(r=>r.live.map(([i,j])=>key(r.id,[i,j]))).sort());
assert(sixes.every(r=>!r.capped&&!r.live.length));assert(fives.every(r=>!r.capped));
const roots=fives.filter(r=>!r.rejected);
const samples=[...roots.filter((r,i)=>i%103===0).slice(0,4),...sixes.filter((r,i)=>i%53===0)];
function base(n,e){
 let b=0;
 for(const [size,lim,c] of [[1,8,2],[2,8,4],[3,8,5],[6,8,6],[10,8,7],
    [4,2,7],[5,2,9],[6,2,11],[4,3,6],[5,3,8],[6,3,10],[5,4,8],[6,4,9]])
   if(n>=size&&e<=lim)b=Math.max(b,c);
 return e<=1?Math.max(b,2*n):b;
}
let checked=0;
for(const r of samples){
 const {gs,ps}=restore(r.id,r.trail);
 const test=prepare(gs,ps,7,true),os=gs.map(table),cost=inspect(os,100).costs;
 const known=new Set(raw.map((_,i)=>(1<<i).toString())),forced=new Map(),ops=[];
 for(let j=0;j<gs.length;j++){
   const pair=ps[j].map(t=>{const v=pm(table(t));if(!known.has(t.toString()))forced.set(t.toString(),v);return v;});
   ops.push(pair);known.add(gs[j].toString());
 }
 const single=Array(13).fill(0),share=[];
 for(const m of forced.values())if(pc[m]===1)single[Math.log2(m)]++;else share.push(m);
 const P=new Uint8Array(8192),floor=new Uint8Array(8192),d=new Int16Array(8192);
 for(let t=1;t<8192;t++){
   const bit=t&-t,i=Math.log2(bit),rest=t^bit;P[t]=P[rest]+Math.max(single[i],cost[i]);floor[t]=floor[rest]+single[i];
   const e=ops.filter(([a,b])=>(t&a&~b)&&(t&b&~a)).length;
   d[t]=base(pc[t],e)+share.filter(m=>!(t&m)).length-P[t];
 }
 // Independently maximize the subset deficit by the standard subset transform.
 for(let b=0;b<13;b++)for(let s=0;s<8192;s++)if(s&1<<b)d[s]=Math.max(d[s],d[s^(1<<b)]);
 for(let s=0;s<8192;s++){
   const privateTotal=P[s]+floor[8191^s];
   const allowed=privateTotal+share.length<=7&&
     (share.length!==0||privateTotal!==7||2*pc[s]<=7)&&privateTotal+d[s]<=7;
   assert.equal(test.fits(s),allowed,'prefix '+key(r.id,r.trail)+' retained '+s);checked++;
 }
}
const result={prefixes:fives.length,eligibleFour:roots.length,fiveTests:fives.reduce((n,r)=>n+r.tested,0),fiveLive:sixes.length,sixTests:sixes.reduce((n,r)=>n+r.tested,0),sixLive:0,capHits:0,compared:samples.map(r=>key(r.id,r.trail)),retainedFamiliesCompared:checked};
fs.writeFileSync(path.join(__dirname,'audit-strong-28.json'),JSON.stringify(result)+'\n');console.log(result);
