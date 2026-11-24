// Generate a DIMACS instance for the full six-gate synthesis problem.
// Run with the project Node executable: node synthesis.cjs [self-test]
'use strict';
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const test = process.argv.includes('self-test');
const count = 6;
const vertices = Array.from({length:10}, (_, i) => i);
const edges = [[0,1],[1,2],[2,3],[3,4],[4,0],[0,5],[1,6],[2,7],[3,8],[4,9],[5,7],[7,9],[9,6],[6,8],[8,5]];
const adjacent = (i,j) => edges.some(([a,b]) => (a===i && b===j)||(a===j && b===i));
const present = (mask,i) => Boolean(mask & (1 << i));
const independent = mask => edges.every(([i,j]) => !present(mask,i) || !present(mask,j));
const zeros = [], positives = new Set();
for (let mask=0; mask<1024; mask++) {
  if (!independent(mask)) continue;
  const extensions = vertices.filter(i => !present(mask,i)).map(i => mask | (1<<i));
  if (extensions.some(independent)) continue;
  zeros.push(mask);
  extensions.forEach(next => positives.add(next));
}
assert.equal(zeros.length,15);
assert.equal(positives.size,100);
let variables=0;
const fresh = () => ++variables;
const clauses = [];
const add = (...clause) => clauses.push(clause);
function disjunction(inputs) {
  const result = fresh();
  for (const input of inputs) add(-input,result);
  add(-result,...inputs);
  return result;
}
function conjunction(a,b) {
  const result = fresh();
  add(-result,a); add(-result,b); add(result,-a,-b);
  return result;
}
const gates = Array.from({length:count},(_,i) =>
  Array.from({length:2},() => Array.from({length:10+i},fresh)));
const output = Array.from({length:count},fresh);
// No variable can be an output selector: every vertex occurs in a zero.
assert(vertices.every(v => zeros.some(mask => present(mask,v))));
// For the self-test pin the six published stars, relaxing just the occurrence cap.
if (test) {
  const centers = [0,1,3,7,8,9];
  gates.forEach(([left,right],i) => {
    left.forEach((s,v) => add(v===centers[i]?s:-s));
    right.forEach((s,v) => add(v<10 && adjacent(centers[i],v)?s:-s));
    add(output[i]);
  });
} else {
  for (const v of vertices) {
    const bare = gates.map(([left,right]) => disjunction([left[v],right[v]]));
    for(let i=0;i<count;i++) for(let j=0;j<i;j++) for(let k=0;k<j;k++) add(-bare[i],-bare[j],-bare[k]);
  }
}
// Wires to earlier gates only; a circuit with fewer gates can pad with unused empty gates.
for(const [mask,expected] of [...zeros.map(m=>[m,false]), ...Array.from(positives,m=>[m,true])]) {
  const values=[];
  for(const sides of gates) {
    const [left,right]=sides.map(selectors => {
      const inputs=vertices.filter(v=>present(mask,v)).map(v=>selectors[v]);
      values.forEach((value,j)=>inputs.push(conjunction(selectors[10+j],value)));
      return disjunction(inputs);
    });
    values.push(conjunction(left,right));
  }
  const result=disjunction(output.map((select,i)=>conjunction(select,values[i])));
  add(expected?result:-result);
}
const name = test ? 'self-test' : 'six-gates';
fs.writeFileSync(path.join(__dirname,name+'.cnf'),['p cnf '+variables+' '+clauses.length,...clauses.map(c=>c.join(' ')+' 0'),''].join('\n'));
fs.writeFileSync(path.join(__dirname,name+'-selectors.json'),JSON.stringify({gates,output}));
console.log({name,variables,clauses:clauses.length,zeros:zeros.length,ones:positives.size});

