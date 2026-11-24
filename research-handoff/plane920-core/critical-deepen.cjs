'use strict';
const fs=require('node:fs'),path=require('node:path'),{runOne}=require('./critical-next.cjs');
const d=path.join(__dirname,'unrestricted'),level=Number(process.argv[2]||6),from=Number(process.argv[3]||0),end=Number(process.argv[4]||1217),cap=Number(process.argv[5]||8000);
const prefix=level===6?'critical-fifth-':'critical-level-'+(level-1)+'-';
const out=path.join(d,'critical-level-'+[level,from,end,cap].join('-')+'.jsonl');
const load=f=>fs.readFileSync(path.join(d,f),'utf8').trim().split('\n').filter(Boolean).map(JSON.parse),key=(id,trail)=>[id,...trail].join(',');
const done=new Set(fs.existsSync(out)?load(path.basename(out)).map(r=>key(r.id,r.trail)):[]);
for(const file of fs.readdirSync(d).filter(f=>f.startsWith(prefix)&&f.endsWith('.jsonl'))){
 for(const r of load(file))if(r.id>=from&&r.id<end)for(const [i,j] of r.live){
    const trail=[...r.trail,i,j],k=key(r.id,trail);if(done.has(k))continue;
    fs.appendFileSync(out,JSON.stringify(runOne(r.id,trail,cap))+'\n');done.add(k);
 }
}

