const assert=require('node:assert/strict');const points=Array.from({length:13},(_,i)=>i);const lines=points.map(i=>[0,1,3,9].reduce((m,x)=>m|1<<((x+i)%13),0));
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

module.exports={group,lines};