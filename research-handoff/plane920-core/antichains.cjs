'use strict';

const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const bits = Array.from({length:8192},(_,z)=>{let n=0; for (;z;z &= z-1) n++; return n;});
const lines = Array.from({length:13},(_,w)=>[0,1,3,9].reduce((z,p)=>z | (1 << ((p+w)%13)),0));
const domain = bits.map((n,z)=>n<=4?z:-1).filter(z=>z>=0);
const includes = (z,t) => (z & t) === t;

// Terms list the inclusion-minimal zero sets on which this wire is false.
function minimal(terms) {
  const sorted=Array.from(new Set(terms)).filter(z=>bits[z]<=4).sort((a,b)=>bits[a]-bits[b] || a-b);
  const result=[];
  for (const z of sorted) if (!result.some(t=>includes(z,t))) result.push(z);
  return result;
}

function antichains(gates) {
  const wires=Array.from({length:13},(_,i)=>[1<<i]);
  for (const [op,...ins] of gates) {
    assert((op==='and' || op==='or') && ins.length<=2);
    const argv=ins.map(i=>wires[i] ?? [0]);
    if (op==='and') wires.push(minimal(argv.flat()));
    else {
      let products=[0];
      for (const terms of argv) products=minimal(products.flatMap(a=>terms.map(b=>a|b)));
      wires.push(products);
    }
  }
  return wires;
}

function direct(gates,z) {
  const wires=Array.from({length:13},(_,p)=>(z & (1<<p))===0);
  for (const [op,...ins] of gates) {
    const values=ins.map(i=>wires[i]??false);
    wires.push(op==='and'? values.every(Boolean) : values.some(Boolean));
  }
  return wires;
}

function audit(gates) {
  const terms=antichains(gates);
  for(const z of domain) {
    const values=direct(gates,z);
    for(let w=0;w<terms.length;w++)
      assert.equal(terms[w].some(t=>includes(z,t)),!values[w], 'zero mask '+z+' wire '+w);
  }
  return terms;
}

const base=[],outputs=[];
for(let w=0;w<13;w++) {
  const [a,b,c,d]=[0,1,3,9].map(v=>(v+w)%13);
  base.push(['or',a,b],['or',c,d]);
  const n=base.length;
  base.push(['or',13+n-2,13+n-1]);
  outputs.push(13+n);
}
const canonical=audit(base);
for(let w=0;w<13;w++) assert.deepEqual(canonical[outputs[w]],[lines[w]]);
assert.equal(new Set(lines).size,13);
for(let a=0;a<13;a++) for(let b=0;b<a;b++) assert.equal(bits[lines[a]&lines[b]],1);
let seed=920;
function rand(n) {seed=(Math.imul(1664525,seed)+1013904223)>>>0; return Math.floor(seed/4294967296*n);}
for(let k=0;k<20;k++){
  const test=[];
  for(let j=0;j<38;j++) test.push([rand(2)?'and':'or',...Array.from({length:rand(3)},()=>rand(16+j))]);
  audit(test);
}
const result={seed:920,domainRows:domain.length,lines:13,baselineGates:base.length,outputs,randomCircuitsCheckedOnEveryWireAndRow:20};
fs.writeFileSync(path.join(__dirname,'antichain-audit.json'),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result));
