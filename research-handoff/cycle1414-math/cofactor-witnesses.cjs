'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');

function edge(mask) {
  for (let i = 0; i < 7; i++) {
    if ((mask & (1 << i)) && (mask & (1 << ((i+1)%7)))) return true;
  }
  return false;
}

const result = [];
for (let p = 0; p < 7; p++) {
  for (let q = 0; q < 7; q++) {
    if (p === q) continue;
    for (const b of [0,1]) {
      const witness = [1,6].map(d => (p+d)%7).map(k => ({
        k, x: (b ? (1<<q) : 0) | (1<<k)
      })).find(({x}) => (x>>q&1)===b && !edge(x));
      assert(witness);
      const x = witness.x, y = x | (1 << p);
      assert.equal(x ^ y, 1 << p);
      assert.equal(x >> p & 1, 0);
      assert.equal(x >> q & 1, b);
      assert.equal(y >> q & 1, b);
      assert.equal(edge(x), false);
      assert.equal(edge(y), true);
      result.push({p,q,b,neighbor:witness.k,x,y});
    }
  }
}
assert.equal(result.length, 84);
const path = 'cofactor-witnesses.json';
fs.writeFileSync(path, JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({verified:result.length,orderedVariablePairs:42,restrictionsPerPair:2,
  witnessChangesOnlyTarget:true,falseToTrueForEveryWitness:true,file:path}));

const gates = [['or',0,2], ['and',1,7], ['or',2,4], ['and',3,9], ['or',4,6],
  ['and',5,11], ['and',6,0], ['or',8,10], ['or',12,13], ['or',14,15]];
let tested=0;
for(let m=0;m<128;m++) {
  const wires=Array.from({length:7},(_,i)=>!!(m>>i&1));
  for(const [op,a,b] of gates) wires.push(op==='and' ? wires[a]&&wires[b] : wires[a]||wires[b]);
  assert.equal(wires[16],edge(m)); tested++;
}
console.log(JSON.stringify({gateCount:gates.length,gateChecks:tested,outputWire:16,gates}));
