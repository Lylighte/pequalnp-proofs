'use strict';
const {signature} = require('./unrestricted-prefix.cjs');
const full = 8191;
const count = new Uint8Array(full + 1);
for (let s = 1; s <= full; s++) count[s] = count[s & (s - 1)] + 1;
// Minimum hidden ANDs for arbitrary complete targets with free OR gates.
const floors = [0,2,4,5,5,6,6,6,6,7,7,7,7,7];
const points = Array.from({length:13}, (_,i) => [1 << i]);
const pointRows = points.map(p => signature(p).active);

function deficits(gs, ps) {
  const known = new Set(points.map(p => p.toString())), losses = new Map();
  for (let i = 0; i < gs.length; i++) {
    for (const a of ps[i]) {
      const key = a.toString();
      if (known.has(key) || losses.has(key)) continue;
      // Replace this forced AND by the free OR of the raw singletons below it.
      // On a named row with one of these points its original value is preserved;
      // on every input the replacement is pointwise below the original gate.
      let preserved = 0;
      for (const t of a) if ((t & (t - 1)) === 0 && t) preserved |= pointRows[31 - Math.clz32(t)];
      losses.set(key, signature(a).active & ~preserved);
    }
    known.add(gs[i].toString());
  }
  const masks = [...losses.values()];
  let needed = floors[13];
  for (let s = 1; s < (1 << masks.length); s++) {
    let affected = 0;
    for (let i = 0; i < masks.length; i++) if (s & (1 << i)) affected |= masks[i];
    const removed = count[s & full] + count[s >>> 13];
    needed = Math.max(needed, removed + floors[count[full & ~affected]]);
  }
  return needed;
}
module.exports = {deficits};
