"use strict";
const {cnf}=require("./two-marked"),fs=require("node:fs"),cp=require("node:child_process"),path=require("node:path"),{lines}=require("./plane-orbits"),{checkProof}=require("../plane920-search/stream-rup.cjs");
(async()=>{
 const dir=path.join(__dirname,"small-core","shared-high"),ls=lines.slice(0,3),raw=ls[0]&~(ls[1]|ls[2]),p=raw&-raw;
 if(ls[0]&ls[1]&ls[2])throw Error("needs triangle");
 for(const h of [4,5]){
  const s=cnf(ls,p,h),stem=path.join(dir,"triangle-onemark-"+h);fs.writeFileSync(stem+".cnf",s);
  const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe",z=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c","190000",stem+".cnf",stem+".lrat"],{encoding:"utf8",windowsHide:true,timeout:20000}),verdict=z.status===20?"UNSAT":z.status===10?"SAT":"UNKNOWN",out={ls,p,h,verdict};
  if(verdict==="UNSAT")out.check=await checkProof(s,stem+".lrat");fs.writeFileSync(stem+".json",JSON.stringify(out,null,2)+"\n");console.log(out);
 }
})().catch(e=>{console.error(e);process.exitCode=1;});
