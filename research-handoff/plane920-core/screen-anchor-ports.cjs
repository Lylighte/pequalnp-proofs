'use strict';
const fs=require('node:fs'),path=require('node:path');
const {prefixes}=require('./three-prefix-all.cjs'),{getArms,join}=require('./unrestricted-prefix.cjs');
const {explain}=require('./anchor-ports.cjs');
const dir=path.join(__dirname,'unrestricted'),from=Number(process.argv[2]),end=Number(process.argv[3]);
const read=f=>{const v=fs.readFileSync(path.join(dir,f),'utf8');return v.slice(0,v.lastIndexOf('\n')+1).trim().split('\n').filter(Boolean).map(JSON.parse);};
const output='anchor-five-v2-29-8-'+from+'-'+end+'.jsonl';
const done=new Set((fs.existsSync(path.join(dir,output))?read(output):[]).map(r=>[r.id,r.i,r.j].join(',')));
for(const f of fs.readdirSync(dir).filter(n=>n.startsWith('early-five-29-8-'))){
  for(const r of read(f)){
    if(r.id<from||r.id>=end||done.has([r.id,r.i,r.j].join(',')))continue;
    const {gs,ps}=prefixes[r.id],a=getArms(gs),four=[a[r.i],a[r.j]],xs=[...gs,join(...four)],ys=[...ps,four],b=getArms(xs);
    const rejected=[];
    for(const [k,l] of r.live){
      const p=[b[k],b[l]];if(!explain([...xs,join(...p)],[...ys,p]).ok)rejected.push([k,l]);
    }
    const out={id:r.id,i:r.i,j:r.j,tested:r.live.length,rejected};
    fs.appendFileSync(path.join(dir,output),JSON.stringify(out)+'\n');
  }
}
