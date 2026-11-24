const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const zlib = require('node:zlib');
const crypto = require('node:crypto');

const lines = Array.from({ length: 13 }, (_, j) =>
  [0, 1, 3, 9].reduce((mask, d) => mask | 1 << ((d + j) % 13), 0));
const points = Array.from({ length: 13 }, (_, v) => v);
const count = n => n.toString(2).replaceAll('0', '').length;
const data = zlib.gunzipSync(fs.readFileSync(path.join(__dirname, 'branch-game-four-records.gz')));
const reference = require('./branch-game-four-exact.json');
assert.equal(crypto.createHash('sha256').update(data).digest('hex'), reference.certificate.sha256);
assert.equal(data.length, reference.counts.critical * 8);

// Enumerate the projective collineations by completing the image of a frame
// using only joins of points and intersections of distinct lines.
const joins = points.map(a => points.map(b => a===b ? 0 : lines.find(L => (L & 1<<a) && (L & 1<<b))));
const frames = [];
for(const a of points) for(const b of points) for(const c of points) for(const d of points){
  if(a===b || (joins[a][b]&1<<c)) continue;
  if((joins[a][b]|joins[a][c]|joins[b][c])&1<<d)continue;
  frames.push([a,b,c,d]);
}
assert.equal(frames.length,5616);
const source=frames[0], construction=[];
const ready=[...source];
while(ready.length<13){
  let step;
  for(const a of ready)for(const b of ready)for(const c of ready)for(const d of ready){
    const cross=joins[a][b]&joins[c][d];
    if(!cross || (cross&(cross-1)))continue;
    const e=31-Math.clz32(cross);
    if(!ready.includes(e))step=[e,a,b,c,d];
  }
  assert(step);construction.push(step);ready.push(step[0]);
}
const group=frames.map(frame=>{
  const p=Array(13);
  source.forEach((v,i)=>p[v]=frame[i]);
  for(const [e,a,b,c,d] of construction)p[e]=31-Math.clz32(joins[p[a]][p[b]]&joins[p[c]][p[d]]);
  assert.equal(new Set(p).size,13);
  for(const L of lines)assert(lines.includes(points.reduce((m,x)=>m|((L&1<<x)?1<<p[x]:0),0)));
  return p;
});
const mapToFirst=[1,2].map(y=>group.filter(p=>(p[0]===0&&p[y]===1)||(p[0]===1&&p[y]===0)));
assert.deepEqual(mapToFirst.map(gs=>gs.length),[72,72]);

const unique = new Set(), orbit = new Set(), profile = {}, observed = {};
const witness = [8,16,32,1,33,24,80,2];
function replay(record){
  const sizes=[],remaining=[],firstMulti=Array(16).fill(0);
  let first=0;
  for(let choices=0;choices<16;choices++){
    let active=lines.map(()=>true);
    const old=[];
    for(let gate=0;gate<4;gate++){
      const arms=record.slice(2*gate,2*gate+2).map(code=>{
        const point=(code>>3)-1, parents=code%8;
        assert(parents<1<<gate && (parents>0 || point>=0));
        return old.reduce((m,v,i)=>m|((parents&1<<i)?v:0),point<0?0:1<<point);
      });
      if(arms.some(m=>m&(m-1))){
        if(!firstMulti[choices])firstMulti[choices]=gate+1;
        if(!first||first>gate+1)first=gate+1;
      }
      const kept=arms[(choices>>gate)&1], dropped=arms[1-((choices>>gate)&1)];
      active=active.map((live,i)=>live && ((lines[i]&kept)===kept||(lines[i]&dropped)!==dropped));
      old.push(kept);
    }
    sizes.push(active.filter(Boolean).length);
    remaining.push(points.filter(i=>active[i]));
  }
  return {best:Math.max(...sizes),first,sizes,remaining,firstMulti};
}
for(let i=0;i<data.length;i+=8){
  const r=Array.from(data.subarray(i,i+8)),key=r.join(',');
  assert(!unique.has(key));unique.add(key);
  const y=(r[1]>>3)-1;
  assert(r[0]===8 && [1,2].includes(y));
  const out=replay(r),label=['0,'+y,out.best,out.first?'mixed':'allStars'].join(':');
  assert(out.best<5);
  profile[label]=(profile[label]||0)+1;
  const histogram=[y,out.best,out.first].join(':');
  observed[histogram]=(observed[histogram]||0)+1;
  let canonical;
  for(const p of mapToFirst[y-1]){
    let key='';
    for(let g=0;g<4;g++){
      const a=r[2*g],b=r[2*g+1],u=(a>>3)?(1+p[(a>>3)-1])*8+a%8:a,v=(b>>3)?(1+p[(b>>3)-1])*8+b%8:b;
      key+=String.fromCharCode(Math.min(u,v),Math.max(u,v));
    }
    if(canonical===undefined||key<canonical)canonical=key;
  }
  orbit.add(canonical);
}
assert.deepEqual(profile,reference.profile);
const orbitDescriptors=Buffer.from([...orbit].sort().join(''),'latin1');
const compact=zlib.gzipSync(orbitDescriptors,{level:9}),orbitHistogram={};
for(let offset=0;offset<orbitDescriptors.length;offset+=8){
  const {best,first}=replay(Array.from(orbitDescriptors.subarray(offset,offset+8)));
  const k=[best,first].join(':');orbitHistogram[k]=(orbitHistogram[k]||0)+1;
}
fs.writeFileSync(path.join(__dirname,'branch-game-four-orbits.gz'),compact);
const result={records:unique.size,syntacticOrbits:orbit.size,groupSize:group.length,
  compact:{bytes:compact.length,sha256:crypto.createHash('sha256').update(orbitDescriptors).digest('hex'),histogram:orbitHistogram},
  rootTransporterSizes:mapToFirst.map(gs=>gs.length),bytes:reference.certificate,profile,
  byFirstMulti:observed,example:{selectors:witness,...replay(witness)}};
assert.equal(result.example.best,3);
fs.writeFileSync(path.join(__dirname,'branch-game-four-replay.json'),JSON.stringify(result,null,2)+'\n');
console.log({records:result.records,syntacticOrbits:result.syntacticOrbits,profile,example:result.example.sizes});
