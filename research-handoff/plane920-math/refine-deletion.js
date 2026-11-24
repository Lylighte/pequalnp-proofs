"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process"),assert=require("node:assert/strict");
const {perm,apply,lines,weight}=require("./plane-orbits.js"),{encode}=require("./small-core.js"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const omit=Number(process.argv[2]??3),lim=Number(process.argv[3]??7),secs=Number(process.argv[4]??45),budget=Number(process.argv[5]??20000);
const prune=process.argv.includes("--prune");
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe",dir=path.join(__dirname,"small-core","deleted");
const file=path.join(dir,"nogoods-"+omit+".json"),log=fs.existsSync(file)?JSON.parse(fs.readFileSync(file,"utf8")):[];
const ids=lines.map((l,i)=>i).filter(i=>!(omit&(1<<i))),gone=lines.filter((l,i)=>omit&(1<<i));
const group=perm.filter(g=>gone.every(l=>gone.includes(apply(l,g))));
const visited=new Set(log.filter(r=>r.verdict!=="UNKNOWN"||((r.budget??20000)>=budget&&Boolean(r.prune)===prune)).flatMap(r=>r.images.map(([u,h])=>[u,h,r.k].join("/"))));
(async()=>{const end=Date.now()+secs*1000;
while(Date.now()<end){
    const run=cp.spawnSync(process.execPath,["--max-old-space-size=1536",path.join(__dirname,"audit-obligations.js"),"seven",String(lim),String(omit)],{encoding:"utf8",timeout:60000,windowsHide:true});
    assert.equal(run.status,0);
    const result=JSON.parse(run.stdout);
    if(!result.full){console.log("closed",omit,lim);break;}
    const cases=result.witness.filter(q=>q.remaining<=4&&weight[q.u]>=3&&weight[q.u]<=12)
        .sort((a,b)=>a.remaining-b.remaining||weight[b.u]-weight[a.u]);
    let changed=false;
    for(const {u,owners:h,remaining:k} of cases){
        if(visited.has([u,h,k].join("/")))continue;
        const fullH=ids.reduce((m,v,i)=>m|((h&(1<<i))?1<<v:0),0),dim=encode(u,k,omit,fullH,prune);
        const stem=path.join(dir,["ng",omit,u,h,k].join("-")+(prune?"-sensitivity":"")),cnf=stem+".cnf",proof=stem+".lrat";
        fs.writeFileSync(cnf,dim);
        const run2=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(budget),cnf,proof],{timeout:45000,windowsHide:true});
        const verdict=run2.status===20?"UNSAT":run2.status===10?"SAT":"UNKNOWN";
        const check=verdict==="UNSAT"?await checkProof(dim,proof):null;
        const images=[...new Set(group.map(g=>{
            const nh=ids.reduce((m,v,i)=>m|((h&(1<<i))?1<<ids.indexOf(lines.indexOf(apply(lines[v],g))):0),0);
            return apply(u,g)*8192+nh;
        }))].map(z=>[z>>13,z&8191]);
        log.push({u,h,k,budget,prune,verdict,images,check});fs.writeFileSync(file,JSON.stringify(log)+"\n");
        for(const [v,o] of images)visited.add([v,o,k].join("/"));
        if(verdict==="UNSAT"){changed=true;break;}
    }
    if(!changed){console.log("no new local rejection");break;}
}
console.log(JSON.stringify({records:log.length,unsat:log.filter(r=>r.verdict==="UNSAT").length}));})().catch(e=>{console.error(e);process.exitCode=1;});
