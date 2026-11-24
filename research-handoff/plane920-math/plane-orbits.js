"use strict";
const fs=require("node:fs"),path=require("node:path"),assert=require("node:assert/strict");
const P=Array.from({length:13},(_,i)=>i),N=8192;
const l=P.map(t=>[0,1,3,9].reduce((m,v)=>m|1<<((v+t)%13),0));
const w=new Uint8Array(N);
for(let u=1;u<N;u++)w[u]=w[u&(u-1)]+1;
const onLine=(p,id)=>Boolean(l[id]&(1<<p));
const join=P.map(i=>P.map(j=>i===j?-1:l.findIndex((_,k)=>onLine(i,k)&&onLine(j,k))));
const meet=P.map(i=>P.map(j=>i===j?-1:Math.log2(l[i]&l[j])));
const frames=[];
for(const a of P)for(const b of P)if(a!==b)for(const c of P)
    if(!onLine(c,join[a][b]))for(const d of P)
        if(!onLine(d,join[a][b])&&!onLine(d,join[a][c])&&!onLine(d,join[b][c]))
            frames.push([a,b,c,d]);
const base=frames[0],perm=[];
for(const fr of frames){
    const p=Array(13).fill(-1),t=Array(13).fill(-1);base.forEach((x,i)=>p[x]=fr[i]);
    for(let k=0;k<13&&p.includes(-1);k++){
        for(let i=0;i<13;i++)for(let j=0;j<i;j++){
            if(p[i]>=0&&p[j]>=0)t[join[i][j]]=join[p[i]][p[j]];
        }
        for(let i=0;i<13;i++)for(let j=0;j<i;j++){
            if(t[i]>=0&&t[j]>=0)p[meet[i][j]]=meet[t[i]][t[j]];
        }
    }
    assert.equal(new Set(p).size,13);assert(!p.includes(-1));
    for(const line of l)assert(l.includes(P.reduce((m,i)=>m|((line&(1<<i))?1<<p[i]:0),0)));
    perm.push(p);
}
assert.equal(perm.length,5616);
const apply=(u,map)=>P.reduce((m,i)=>m|((u&(1<<i))?1<<map[i]:0),0);
const dir=path.join(__dirname,"small-core");
function classify(n,h){
    const file=path.join(dir,"results-"+n+"-"+h+".json");
    if(!fs.existsSync(file))return null;
    const data=JSON.parse(fs.readFileSync(file,"utf8")).records;
    const all=data.flatMap(r=>r.orbit);assert.equal(new Set(all).size,all.length);
    const seen=new Set(),groups=[];
    for(const {u} of data)if(!seen.has(u)){
        const orbit=new Set(perm.map(g=>apply(u,g))),rr=data.filter(r=>orbit.has(r.u));
        const truths=new Set(rr.map(r=>r.verdict));assert.equal(truths.size,1);
        for(const k of orbit)seen.add(k);
        const choices=rr.map(r=>{
            const f=path.join(dir,r.u+"-"+h+".lrat");
            return {u:r.u,proofBytes:fs.existsSync(f)?fs.statSync(f).size:0};
        }).sort((a,b)=>a.proofBytes-b.proofBytes||a.u-b.u);
        const rep=choices[0].u;
        const maps=rr.map(r=>({u:r.u,imageFrame:frames[perm.findIndex(g=>apply(r.u,g)===rep)]}));
        groups.push({rep,verdict:rr[0].verdict,orbitSize:orbit.size,proofBytes:choices[0].proofBytes,maps});
    }
    assert.equal(seen.size,all.length);return groups;
}
module.exports={perm,apply,lines:l,weight:w,frames,base};
if(require.main===module){
const sets={};
for(const n of [5,6,7])for(const h of [1,2,3]){const r=classify(n,h);if(r)sets[n+"-"+h]=r;}
fs.writeFileSync(path.join(dir,"full-orbits.json"),JSON.stringify({baseFrame:base,automorphisms:perm.length,sets},null,2)+"\n");
console.log(JSON.stringify(Object.fromEntries(Object.entries(sets).map(([k,r])=>[k,r.map(s=>[s.rep,s.orbitSize,s.verdict,s.proofBytes])]))));
}
