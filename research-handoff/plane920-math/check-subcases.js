"use strict";

const assert = require("node:assert/strict");
const size = x => x.toString(2).replace(/0/g, "").length;
const subset = (a, b) => (a & b) === a;
const lines = Array.from({length: 13}, (_, w) =>
    [0, 1, 3, 9].reduce((a, u) => a | (1 << ((u + w) % 13)), 0));
const domain = Array.from({length: 1 << 13}, (_, i) => i).filter(a => size(a) <= 4);
const contained = domain.filter(a => a && lines.some(line => subset(a, line)));
for (const a of lines) {
    assert.equal(size(a), 4);
    for (const b of lines) if (b !== a) assert.equal(size(a & b), 1);
}
let local = 0, singleton = 0, bothLarge = 0, twoLines = 0;
for (const a of contained) for (const b of contained) {
    const viable = [];
    for (const line of lines) {
        if (!subset(a, line) && !subset(b, line)) continue;
        let witnesses = 0;
        for (let c = line;; c = (c - 1) & line) {
            const u = a | c, v = b | c;
            if ((u === line || v === line) &&
                (u === line || size(u) > 4) && (v === line || size(v) > 4)) {
                local++;
                witnesses++;
                if (size(a) === 1) {
                    singleton++;
                    assert(u === line || c === line);
                }
            }
            if (!c) break;
        }
        if (witnesses) viable.push(line);
    }
    if (size(a) >= 2 && size(b) >= 2) {
        bothLarge++;
        assert(viable.length <= 2);
        if (viable.length === 2) {
            twoLines++;
            assert.equal(size(viable[0] & viable[1]), 1);
        }
    }
}
// An operand never contained in a target line cannot provide its positive witness.
// One arbitrary operand of size up to four does not alter the singleton implication.
let singleArbitrary = 0;
for (const a of contained.filter(x => size(x) === 1)) for (const b of domain)
    for (const l of lines) for (let c = l;; c = (c - 1) & l) {
        const u = a | c, v = b | c;
        if ((u === l || v === l) && (u === l || size(u) > 4) &&
            (v === l || size(v) > 4)) {
            assert(u === l || c === l);
            singleArbitrary++;
        }
        if (!c) break;
    }
// Independently check the 39-gate reference circuit on every permitted input row.
let cells = 0;
for (const row of domain) for (const line of lines) {
    const [a,b,c,d] = Array.from({length:13}, (_, i) => 1 << i).filter(p => p & line);
    const first = Boolean(row & a) && Boolean(row & b);
    const second = Boolean(row & c) && Boolean(row & d);
    assert.equal(first && second, row === line);
    cells++;
}
console.log(JSON.stringify({lines: lines.length, rows: domain.length, referenceCells: cells,
    nonemptyLineSubsets: contained.length, admissibleOrderedSwitchAndContext: local,
    singletonAdmissible: singleton, twoLargeOrdered: bothLarge,
    twoLargeWithTwoViableLines: twoLines, singletonArbitraryOperandAdmissible: singleArbitrary}, null, 2));
