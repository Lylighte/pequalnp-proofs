'use strict';
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const n = 13;
const lines = Array.from({length:n}, (_,w)=>[0,1,3,9].reduce((m,p)=>m | (1<<((p+w)%n)),0));
function count(mask) {let k=0;for(;mask;mask &= mask-1) k++;return k;}
let best = 0; const winners = [];
for (let mask=1;mask<(1<<n);mask++) {
  let covered = 0;
  for (let w=0;w<n;w++) if(mask & (1<<w)) covered |= lines[w];
  const bound = count(covered)-1+n-count(mask);
  if (bound > best) {best=bound;winners.length=0;}
  if (bound === best) winners.push(mask);
}
const pencils = Array.from({length:n},(_,p)=>lines.reduce((mask,line,w)=>mask|((line & (1<<p))?(1<<w):0),0));
assert.equal(best,21);
assert.deepEqual(winners,pencils.sort((a,b)=>a-b));
const r={subsets:(1<<n)-1,bestBound:best,attainedExactlyByPencils:winners.length,winningMasks:winners};
fs.writeFileSync(path.join(__dirname,'pencil-count.json'),JSON.stringify(r,null,2)+'\n');
console.log(JSON.stringify(r));
