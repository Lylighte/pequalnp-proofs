'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {record,next,can,join,getArms}=require('./unrestricted-prefix.cjs');
const dir=path.join(__dirname,'unrestricted'),total=Number(process.argv[2]||27),h=Number(process.argv[3]||7);
const tag=process.argv[4]||'5678',out=path.join(dir,'sixth-'+total+'-'+h+'.jsonl');
const seen=new Set((fs.existsSync(out)?fs.readFileSync(out,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).id));
for(const file of fs.readdirSync(dir).filter(f=>f.startsWith('round-'+total+'-'+tag+'-'))){
  const lines=fs.readFileSync(path.join(dir,file),'utf8').trimEnd().split('\n').filter(Boolean);
  for(const line of lines){
    const r=JSON.parse(line);if(seen.has(r.id))continue;
    const runs=[];
    for(const [i,j,active] of r.live)if(active.includes(h)){
      const {gates,pairs}=record(r.id),arms=getArms(gates),pair5=[arms[i],arms[j]],g5=[...gates,join(...pair5)],p5=[...pairs,pair5];
      let checked=0;const unresolved=[];
      next(g5,p5,(gs,ps,a,b)=>{checked++;if(can(gs,ps,[h],total).length)unresolved.push([a,b]);});
      runs.push({i,j,checked,unresolved});
    }
    fs.appendFileSync(out,JSON.stringify({id:r.id,runs})+'\n');
  }
}

