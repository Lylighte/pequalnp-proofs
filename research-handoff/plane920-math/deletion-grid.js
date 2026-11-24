"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process"),assert=require("node:assert/strict");
const orbits=require("./small-core/dropped-orbits.json"),dir=__dirname,output=path.join(dir,"small-core","deleted","grid.json");
const sets=process.argv.slice(2).map(s=>s.split(",").map(Number));
const rows=fs.existsSync(output)?JSON.parse(fs.readFileSync(output,"utf8")):{};
for(const [count,cap] of sets)for(const {u,size} of orbits[count]){
    const transfer=path.join(dir,"small-core","deleted","transferred-"+u+".json");
    if(!fs.existsSync(transfer)){
        const t=cp.spawnSync(process.execPath,[path.join(dir,"transfer-certs.js"),String(u)],{timeout:60000,windowsHide:true});
        assert.equal(t.status,0);
    }
    const v=cp.spawnSync(process.execPath,["--max-old-space-size=1536",path.join(dir,"audit-obligations.js"),"seven",String(cap),String(u)],{timeout:65000,windowsHide:true,encoding:"utf8"});
    if(v.status!==0){console.log("pending",u,cap,v.status);continue;}
    const r=JSON.parse(v.stdout);rows[u+","+cap]={dropped:u,count,size,cap,feasible:r.full,states:r.states};
    fs.writeFileSync(output,JSON.stringify(rows,null,2)+"\n");
    console.log(u,cap,r.full,r.states);
}
