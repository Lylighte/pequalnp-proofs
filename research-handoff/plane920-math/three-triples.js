"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process"),{cnf}=require("./two-marked"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const w=s=>s.toString(2).replace(/0/g,"").length,dir=path.join(__dirname,"small-core","shared-high"),bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
(async()=>{
 for(let sig=0;sig<=8;sig++){
  const sets=[0,0,0];let pt=0;
  if(sig===8){sets.fill(1);pt++;}
  else{for(const [i,[a,b]] of [[0,1],[0,2],[1,2]].entries())if(sig>>i&1){sets[a]|=1<<pt;sets[b]|=1<<pt;pt++;}}
  const marks=[];for(let i=0;i<3;i++){marks[i]=1<<pt;while(w(sets[i])<3)sets[i]|=1<<pt++;}
  for(const h of [3]){
   const stem=path.join(dir,"three-triples-twomarks-"+sig+"-"+h),s=cnf(sets,marks[0]|marks[1],h,3);fs.writeFileSync(stem+".cnf",s);
   const p=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c","90000",stem+".cnf",stem+".lrat"],{encoding:"utf8",windowsHide:true,timeout:10000});
   const verdict=p.status===20?"UNSAT":p.status===10?"SAT":"UNKNOWN",r={sig,h,sets,marks:marks.slice(0,2),verdict};if(verdict==="UNSAT")r.check=await checkProof(s,stem+".lrat");fs.writeFileSync(stem+".json",JSON.stringify(r,null,2)+"\n");console.log(sig,verdict,r.check?.add);
  }
 }
})().catch(e=>{console.error(e);process.exitCode=1;});
