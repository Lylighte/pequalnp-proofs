"use strict";
const fs=require("node:fs"),path=require("node:path");
const {perm,apply,lines,weight}=require("./plane-orbits.js");
const target=Number(process.argv[2]??7),ids=Array.from({length:13},(_,i)=>i),dir=path.join(__dirname,"small-core","deleted");
const maps=perm.map(g=>lines.map(l=>lines.indexOf(apply(l,g))));
const toComp=(mask,drop)=>ids.filter(i=>!(drop&(1<<i))).reduce((s,i,j)=>s|((mask&(1<<i))?1<<j:0),0);
const fromComp=(mask,drop)=>ids.filter(i=>!(drop&(1<<i))).reduce((s,i,j)=>s|((mask&(1<<j))?1<<i:0),0);
const image=(mask,m)=>{let s=0;for(let i=mask;i;i&=i-1)s|=1<<m[Math.log2(i&-i)];return s;};
const result=new Map();
function use(u,omit,h,k){
    const req=lines.reduce((s,l,i)=>s|((!(omit&(1<<i))&&weight[l&u]>=3)?1<<i:0),h);
    for(let i=0;i<maps.length;i++){
        if(image(req,maps[i])&target)continue;
        const v=apply(u,perm[i]),z=toComp(image(h,maps[i]),target),key=v*8192+z;
        if((result.get(key)??0)<k+1)result.set(key,k+1);
    }
}
for(const name of fs.readdirSync(dir)){
    const n=name.match(/^(\d+)-(\d+)-(\d+)\.json$/),g=name.match(/^nogoods-(\d+)\.json$/);
    if(!n&&!g)continue;
    const d=Number(n?n[3]:g[1]);if(d===target)continue;
    const rows=JSON.parse(fs.readFileSync(path.join(dir,name),"utf8"));
    for(const r of rows)if(r.verdict==="UNSAT"&&r.check?.empty)use(r.u,d,g?fromComp(r.h,d):0,n?Number(n[2]):r.k);
}
const values=[...result].map(([key,b])=>[Math.floor(key/8192),key%8192,b]);
fs.writeFileSync(path.join(dir,"transferred-"+target+".json"),JSON.stringify(values)+"\n");
console.log(JSON.stringify({target,valid:values.length}));
