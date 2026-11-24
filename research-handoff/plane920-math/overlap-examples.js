"use strict";
const assert = require("node:assert/strict");
const lines = Array.from({length:13}, (_, w) =>
    [0,1,3,9].reduce((a,u) => a | (1 << ((u+w)%13)), 0));
const pop = x => x.toString(2).replace(/0/g, "").length;
const rows = Array.from({length:8192}, (_, i) => i).filter(x => pop(x) <= 4);
const bit = i => 1<<i;
const contains = (a,b) => (a & b) === b;
const L = lines[0];
function check(name, gates, expectedHybrid) {
    const sols = gates.map(() => []);
    const refs = (row, i) => Boolean(row & bit(i));
    for (const row of rows) {
        const vals = Array.from({length:13}, (_, i) => refs(row, i));
        for (const [k, [op, x, y]] of gates.entries()) {
            const res = op === "and" ? vals[x] && vals[y] : vals[x] || vals[y];
            vals.push(res);
            if (res) sols[k].push(row);
        }
        assert.equal(vals.at(-1), row === L);
    }
    let hybridCount = 0;
    const inspections = sols.map((s, i) => {
        const size = Math.min(...s.map(pop));
        const mins = s.filter(x => pop(x) === size);
        const pos = lines.map((x, j) => [x,j]).filter(([x]) => s.includes(x)).map(([,j]) => j);
        const owner = pos.includes(0) && (pos.length === 1 ||
            (mins.length === 1 && size>=2 && contains(L, mins[0])));
        hybridCount += Number(owner);
        return {wire:13+i, trueLineIds:pos, minimumSize:size, minimumWitnessCount:mins.length, owner};
    });
    assert.equal(hybridCount, expectedHybrid);
    return {name, domainRows:rows.length, gateCount:gates.length, gates, hybridCount, inspections};
}
const six = check("one repeated point", [
    ["or",0,2], ["or",0,4], ["and",13,1], ["and",15,3], ["and",14,9], ["and",16,17]
], 2);
const five = check("row-only counterexample with a clean proof", [
    ["and",2,4], ["or",0,13], ["and",14,1], ["and",3,9], ["and",15,16]
], 3);
const p = 9, c = 3, a = 0, b = 1;
const m = lines.find(x=>x!==L && contains(x,bit(p)));
const n = lines.find(x=>x!==L && x!==m && contains(x,bit(c)));
const pts = mask => Array.from({length:13}, (_,i)=>i).filter(i => mask & bit(i));
const [d,e] = pts(m & ~L & ~n), [u,v] = pts(n & ~L & ~m);
assert.equal(new Set([p,c,a,b,d,e,u,v]).size, 8);
const nine = check("two repeated points", [
    ["or",a,d],["or",b,e],["and",13,14],["and",15,p],
    ["or",a,u],["or",b,v],["and",17,18],["and",19,c],["and",16,20]
],1);
console.log(JSON.stringify([five,six,nine], null, 2));
