"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const assert=require("node:assert/strict");
const {checkProof}=require("../plane920-search/stream-rup.cjs");
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
const helpers=Number(process.argv[2]??2);
const n=Number(process.argv[3]??7);
const dir=path.join(__dirname,"small-core"),data=require("./small-core/results-"+n+"-"+helpers+".json");
(async()=>{
    const receipts=[];
    for(const {u,orbit,verdict} of data.records){
        if(verdict==="SAT")continue;
        assert.equal(verdict,"UNSAT");
        const cnf=path.join(dir,u+"-"+helpers+".cnf"),proof=path.join(dir,u+"-"+helpers+".lrat");
        const ans=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary",cnf,proof],{windowsHide:true,timeout:18000});
        assert.equal(ans.status,20);
        const checked=await checkProof(fs.readFileSync(cnf,"utf8"),proof);
        receipts.push({u,orbitSize:orbit.length,...checked});
    }
    const summary={orbits:receipts.length,covered:receipts.reduce((s,r)=>s+r.orbitSize,0),receipts};
    const all=Array.from({length:8192},(_,u)=>u).filter(u=>u.toString(2).replaceAll("0","").length===n);
    assert.equal(new Set(data.records.flatMap(r=>r.orbit)).size,all.length);
    const dest=n!==7?"replay-"+n+"-"+helpers+".json":helpers===2?"replay.json":"replay-"+helpers+".json";
    fs.writeFileSync(path.join(dir,dest),JSON.stringify(summary,null,2)+"\n");
    console.log(JSON.stringify({orbits:summary.orbits,covered:summary.covered,adds:receipts.reduce((s,r)=>s+r.add,0)}));
})().catch(err=>{console.error(err);process.exitCode=1;});
