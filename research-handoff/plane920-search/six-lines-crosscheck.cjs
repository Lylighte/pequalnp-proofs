const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const {orbits, next, table, mult, join, raw, loc, lines, pc, perm, rel, univ, pm} = require('./three-or-five-lines.cjs');
const {inspect} = require('./private-independent.cjs');

const initial = [1, 2];
const stabilizer = perm.filter(p => rel(initial, p) === '1,2');
const roots = [];
for (const second of orbits(next([initial], true), stabilizer)) {
  for (const third of orbits(next([initial, second.t], true), second.stab)) {
    roots.push([initial, second.t, third.t]);
  }
}
assert.equal(roots.length, 1897);

const domain = Array.from({length: 8192}, (_, i) => i).filter(x => pc[x] <= 4);
let seed = 314159265;
function index(n) { seed = (Math.imul(1664525, seed) + 1013904223) >>> 0; return seed % n; }
const tally = {roots: 0, arms: 0, products: 0, positiveTests: 0, admitted: 0};
for (let k = 0; k < 19; k++) {
  const terms = roots[(97*k+65)%roots.length], named = new Set(terms.map(t => t.join(',')));
  const flags = terms.map(table);
  const opts = new Map();
  for (let p = -1; p < 13; p++) for (let bits = 0; bits < 8; bits++) {
    if (p < 0 && bits === 0) continue;
    let t = [p < 0 ? 0 : 1 << p];
    for (let g = 0; g < 3; g++) if (bits & 1 << g) t = mult(t, terms[g]);
    if (pc[t.reduce((a, b) => a & b, 8191)] > 1) continue;
    const w = table(t), pos = pm(w);
    if (pc[pos] < 2 && !(t.length === 1 && pc[t[0]] === 1) && !named.has(t.join(','))) continue;
    opts.set(t.join(','), {t, w, pos});
  }
  tally.roots++;
  tally.arms += opts.size;
  const arms = [...opts.values()];
  for (let sample = 0; sample < 69; sample++) {
    const a = arms[index(arms.length)], b = arms[index(arms.length)], union = a.pos | b.pos;
    if (union === a.pos || union === b.pos) continue;
    const bits = [...flags, a.w | b.w];
    const allTerms = [...terms, join(a.t, b.t)];
    const exact = inspect(bits, 100).costs;
    tally.products++;
    // Independently evaluate the monotone DNFs on every ordinary integer input.
    const values = domain.map(input => allTerms.reduce((v, term, j) =>
      v | (term.some(m => (m & input) === m) ? 1 << j : 0), 0));
    for (let i = 0; i < 13; i++) {
      const L = lines[i], at = values[domain.indexOf(L)], pts = [];
      for (let q = 0; q < 13; q++) if (L & 1 << q) pts.push(q);
      const old = flags.reduce((v, w) => (w & loc[i]) ? v & w : v, univ);
      for (const arity of [2, 3]) {
        let split = false, direct = false;
        for (let sub = L; sub; sub = (sub-1)&L) {
          if (pc[sub] !== arity) continue;
          // Direct pointwise truth-table test of the proposed strongest product.
          if (!domain.some((input, ix) => input !== L && (input & sub) === sub &&
                (values[ix] & at) === at)) direct = true;
          let w = old;
          for (const q of pts) if (sub & 1 << q) w &= raw[q];
          const bad = w ^ loc[i];
          if (bad === 0n || ((union & 1 << i) && !(bad & a.w) && !(bad & b.w))) split = true;
        }
        assert.equal(split, direct);
        if (exact[i] <= arity-2) assert(direct);
        if (direct) tally.admitted++;
        tally.positiveTests++;
      }
    }
  }
}
fs.writeFileSync(path.join(__dirname, 'six-lines-crosscheck.json'), JSON.stringify(tally) + '\n');
console.log(tally);
