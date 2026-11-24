"use strict";
const fs=require("node:fs"),path=require("node:path"),base=path.join(__dirname,"small-core");
const data=fs.readdirSync(path.join(base,"four-five-partial")).filter(x=>x.endsWith(".json")).map(x=>JSON.parse(fs.readFileSync(path.join(base,"four-five-partial",x))));
const cert=new Set(data.filter(x=>x.verdict==="UNSAT").map(x=>[x.S,...x.pre].join("-")));
const recs=JSON.parse(fs.readFileSync(path.join(base,"four-target-five-signatures.json"))).map(z=>({S:z.S,total:z.rows.length,unresolved:z.rows.filter(row=>!row.some((_,i)=>cert.has([z.S,...row.slice(0,i+1)].join("-")))).length}));
const statuses={};for(const r of data){const k=r.pre.length+"-"+r.verdict;statuses[k]=(statuses[k]||0)+1;}
const result={note:"Stopped all local probes when session reserve reached 15 percent; coverage is an intermediate classified-signature count, not a completed four-target lower bound.",statuses,recs};
fs.writeFileSync(path.join(base,"four-five-checkpoint.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(recs));
