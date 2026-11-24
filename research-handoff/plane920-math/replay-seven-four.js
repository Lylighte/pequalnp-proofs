"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process"),assert=require("node:assert/strict");
const {checkProof}=require("../plane920-search/stream-rup.cjs");
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
const dir=path.join(__dirname,"small-core"),outFile=path.join(dir,"replay-seven-four.json");
const orbits=require("./small-core/full-orbits.json").sets["7-3"];
const receipts=fs.existsSync(outFile)?JSON.parse(fs.readFileSync(outFile,"utf8")):[];
(async()=>{
    for(const {rep,orbitSize} of orbits) {
        if(rep===719||receipts.some(x=>x.rep===rep))continue;
        const cnf=path.join(dir,rep+"-4.cnf"),proof=path.join(dir,rep+"-4.lrat");
        const run=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary",cnf,proof],{timeout:90000,windowsHide:true});
        assert.equal(run.status,20);
        const checked=await checkProof(fs.readFileSync(cnf,"utf8"),proof);
        receipts.push({rep,orbitSize,bytes:fs.statSync(proof).size,...checked});
        fs.writeFileSync(outFile,JSON.stringify(receipts,null,2)+"\n");
        console.log(JSON.stringify(receipts.at(-1)));
    }
})().catch(err=>{console.error(err);process.exitCode=1;});
