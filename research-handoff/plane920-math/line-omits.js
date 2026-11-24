"use strict";
const fs=require("node:fs"),path=require("node:path"),{perm,apply,lines,weight}=require("./plane-orbits.js");
const maps=perm.map(g=>lines.map(l=>lines.indexOf(apply(l,g))));
function im(u,m){let v=0;for(let s=u;s;s&=s-1)v|=1<<m[Math.log2(s&-s)];return v;}
const seen=new Set(),groups={};
for(const u of [1,3,7,35,23,39,5137,...Array.from({length:8192},(_,i)=>i)]){
    if(seen.has(u)||weight[u]>8)continue;
    const orbit=new Set(maps.map(m=>im(u,m)));
    for(const v of orbit)seen.add(v);
    (groups[weight[u]]??=[]).push({u,size:orbit.size});
}
fs.writeFileSync(path.join(__dirname,"small-core","dropped-orbits.json"),JSON.stringify(groups,null,2)+"\n");
console.log(JSON.stringify(groups));
