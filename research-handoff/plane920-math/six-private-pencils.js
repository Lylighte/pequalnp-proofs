"use strict";
const fs=require("node:fs"),path=require("node:path"),{lines,weight:w}=require("./plane-orbits");
const pencils=lines.map((_,p)=>lines.reduce((r,l,i)=>r|((l>>p&1)<<i),0));
let checked=0;const failures=[],records={};
for(let r=0;r<8192;r++)if(w[r]===6){
 let pr=0;for(const pencil of pencils){const a=r&pencil;if(w[a]===1)pr|=a;}
 if(pr!==r)continue;checked++;
 let maximum=0;for(const p of pencils)for(const q of pencils)maximum=Math.max(maximum,w[r&(p|q)]);
 records[maximum]=(records[maximum]||0)+1;if(maximum===6)failures.push(r);
}
const out={checked,maximumTwoPencils:records,failures};console.log(out);
fs.writeFileSync(path.join(__dirname,"small-core","six-private-pencils.json"),JSON.stringify(out,null,2)+"\n");
