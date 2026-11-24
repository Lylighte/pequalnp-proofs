'use strict';
const {signature} = require('./unrestricted-prefix.cjs');
const {baseAnd} = require('./effective-cut.cjs');
const {deficits} = require('./paid-deficits.cjs');
const full = 8191, pc = new Uint8Array(full+1);
for (let s=1;s<=full;s++) pc[s]=1+pc[s&(s-1)];
const free = [0,2,4,5,5,6,6,6,6,7,7,7,7,7];
const floors = Array.from({length:11},(_,e) => free.map((v,n) =>
  Math.max(v,baseAnd(n,e), n>=5 && e<=4 ? 8 : 0, n>=6 && e<=4 ? 9 : 0)));
const newFloors=floors.map((row,e)=>row.map((v,n)=>Math.max(v,
  n>=4&&e<=3?7:0,n>=5&&e<=3?9:0,n>=6&&e<=3?11:0,
  n>=4&&e<=4?6:0,n>=6&&e<=4?10:0,n>=7&&e<=5?9:0)));
const top = Array.from({length:13},(_,i)=>String(1<<i));

// Keep the rows on which each original OR takes its original value after
// choosing its indicated arm. Every wire keeps its original value there.
// Each compulsory earlier AND becomes a raw monomial. If it accepts two
// retained rows it is at most a single point, since distinct lines meet once.
function bounds(gs,ps,hs,updated=false) {
  const prices=updated?newFloors:floors;
  const result = Object.fromEntries(hs.map(h=>[h,deficits(gs,ps)]));
  let families=[full];
  const known=new Set(top), paid=new Map();
  for(let j=0;j<gs.length;j++){
    const [a,b]=ps[j].map(signature);
    for(const arm of [a,b]) if(!known.has(arm.key)) paid.set(arm.key,arm.active);
    known.add(gs[j].toString());
    const next=new Set();
    for(const s of families){next.add(s&~(a.active&~b.active));next.add(s&~(b.active&~a.active));}
    families=[...next];
    for(const s of families){
      let costs=0; const live=[];
      for(const m of paid.values()){
        const z=m&s;
        if(pc[z]===1)live.push(z);else costs++;
      }
      // A singleton-active survivor is also removable when its one row
      // is discarded. For each retained cardinality, discard the rows with
      // the largest multiplicities first to maximize the additional savings.
      const tally=new Uint8Array(13);
      for(const z of live)tally[31-Math.clz32(z)]++;
      const order=Array.from({length:13},(_,i)=>i).filter(i=>s&(1<<i)).map(i=>tally[i]).sort((u,v)=>v-u);
      for(let n=order.length;n>0;n--){
        for(const h of hs) if(h>=j+1)result[h]=Math.max(result[h],costs+prices[h-j-1][n]);
        costs+=order[order.length-n];
      }
    }
  }
  return result;
}
module.exports={bounds};
