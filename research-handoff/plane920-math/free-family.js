"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process"),{encode}=require("./small-core.js"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const lineMask=Number(process.argv[2]),helpers=Number(process.argv[3]),budget=Number(process.argv[4]??75000),prune=process.argv.includes("--prune");
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,p)=>m|1<<((i+p)%13),0));
const u=lines.reduce((m,l,i)=>m|((lineMask&(1<<i))?l:0),0),omit=8191^lineMask,cover4=process.argv.includes("--cover4");
const dimacs=encode(u,helpers,omit,0,prune,cover4);
const stem=path.join(__dirname,"small-core","deleted","family-"+lineMask+"-"+helpers+(prune?"-s":"")+(cover4?"-cover4":"")+"-"+budget),cnf=stem+".cnf",proof=stem+".lrat";
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
(async()=>{
    fs.writeFileSync(cnf,dimacs);
    const run=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(budget),cnf,proof],{timeout:65000,windowsHide:true});
    const verdict=run.status===20?"UNSAT":run.status===10?"SAT":"UNKNOWN";
    const check=verdict==="UNSAT"?await checkProof(dimacs,proof):null;
    const rec={lineMask,u,helpers,budget,prune,cover4,verdict,check};
    fs.writeFileSync(stem+".json",JSON.stringify(rec,null,2)+"\n");console.log(JSON.stringify(rec));
})().catch(e=>{console.error(e);process.exitCode=1;});
