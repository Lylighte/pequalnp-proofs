'use strict';

// Recover the original input clauses actually read by the trimmed RUP proof.
// Keep DIMACS clause IDs fixed for a second replay by replacing every unreferenced
// clause with a duplicate of one referenced clause. This removes their constraints.
const fs = require('node:fs');
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const path = require('node:path');
const hash = b => crypto.createHash('sha256').update(b).digest('hex');
const file = name => path.join(__dirname, name);
const trace = fs.readFileSync(file('../petersen-kernel-test/orbit-15-593.trimmed.lrat'));
const input = fs.readFileSync(file('orbit-15-593.cnf'));
assert.equal(hash(input), '6d5240f45e1c25be6ecfa941e9da3b7cfa09473d79a92caa37acfdc257bc9230');
assert.equal(hash(trace), '79aa19354eedd8ccdb47d45e03a1a0a7b28aa49d116efba0ff3b08c9c025aa00');
const lines = input.toString('utf8').trimEnd().split('\n');
const clauseCount = lines.length - 1;
const needed = new Set();
let offset = 0, additions = 0, deletions = 0;
function signedWord() {
  let value = 0, scale = 1, byte;
  do {
    assert(offset < trace.length);
    byte = trace[offset++];
    value += (byte & 127) * scale;
    scale *= 128;
  } while (byte & 128);
  assert(Number.isSafeInteger(value));
  return (value % 2 ? -1 : 1) * Math.floor(value / 2);
}
while (offset < trace.length) {
  const op = trace[offset++];
  if (op === 100) {
    while (signedWord() !== 0) {}
    deletions++;
    continue;
  }
  assert.equal(op, 97);
  assert(signedWord() > clauseCount);
  while (signedWord() !== 0) {}
  for (let hint; (hint = signedWord()) !== 0;) {
    assert(hint > 0, 'Only positive RUP hints are supported by this audit');
    if (hint <= clauseCount) needed.add(hint);
  }
  additions++;
}
const labels = lines.map((s,i) => ({s,i})).filter(x => /^-?\d+ 0$/.test(x.s) && x.i <= clauseCount - 20);
assert.equal(labels.length, 115);
const inCore = xs => xs.filter(x => needed.has(x.i)).length;
const fallback = lines[Math.min(...needed)];
const padded = lines.map((text, id) => id === 0 || needed.has(id) ? text : fallback).join('\n') + '\n';
fs.writeFileSync(file('orbit-15-593.core-padded.cnf'), padded);
const report = {
  originalClauses: clauseCount, retainedIds: needed.size, negativeRowsUsed: inCore(labels.slice(0,15)),
  positiveRowsUsed: inCore(labels.slice(15)), additions, deletions,
  inputSHA256: hash(input), trimmedProofSHA256: hash(trace), paddedCoreSHA256: hash(padded),
  retainedLabelClauseIds: labels.filter(x => needed.has(x.i)).map(x => x.i)
};
fs.writeFileSync(file('orbit-15-593.core.json'), JSON.stringify(report, null, 2) + '\n');
console.log(report.retainedIds, report.negativeRowsUsed, report.positiveRowsUsed, report.paddedCoreSHA256);