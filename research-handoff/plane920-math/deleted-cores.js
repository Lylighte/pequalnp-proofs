"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process"),assert=require("node:assert/strict");
const {perm,apply,lines,weight}=require("./plane-orbits.js");
const {encode}=require("./small-core.js"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const n=Number(process.argv[2]??7),h=Number(process.argv[3]??3),omit=Number(process.argv[4]??3);
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe",dir=path.join(__dirname,"small-core","deleted");
fs.mkdirSync(dir,{recursive:true});
const out=path.join(dir,[n,h,omit].join("-")+".json"),records=fs.existsSync(out)?JSON.parse(fs.readFileSync(out,"utf8")):[];
const omitLines=lines.filter((_,i)=>omit&(1<<i));
const group=perm.filter(g=>omitLines.every(l=>omitLines.includes(apply(l,g))));
const covered=new Set(records.flatMap(r=>r.orbit));
(async()=>{
for(let u=1;u<8192;u++)if(weight[u]===n&&!covered.has(u)){
    const orbit=[...new Set(group.map(g=>apply(u,g)))].sort((a,b)=>a-b),text=encode(u,h,omit);
    const stem=path.join(dir,[u,h,omit].join("-")),file=stem+".cnf",proof=stem+".lrat";
    fs.writeFileSync(file,text);
    const run=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c","35000",file,proof],{windowsHide:true,timeout:45000});
    const verdict=run.status===20?"UNSAT":run.status===10?"SAT":"UNKNOWN";
    const check=verdict==="UNSAT"?await checkProof(text,proof):null;
    const r={u,orbit,verdict,check};records.push(r);fs.writeFileSync(out,JSON.stringify(records)+"\n");
    orbit.forEach(i=>covered.add(i));
}
assert.equal(covered.size,Array.from({length:8192},(_,u)=>u).filter(u=>weight[u]===n).length);
console.log(JSON.stringify({n,h,omit,group:group.length,orbits:records.length,counts:records.reduce((s,r)=>(s[r.verdict]=(s[r.verdict]??0)+r.orbit.length,s),{})}));
})().catch(e=>{console.error(e);process.exitCode=1;});
