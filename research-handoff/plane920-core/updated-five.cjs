'use strict';
const fs=require('node:fs'),path=require('node:path');
const {prefixes}=require('./three-prefix-all.cjs'),{getArms,join}=require('./unrestricted-prefix.cjs');
const {bounds}=require('./early-fold.cjs');
const dir=path.join(__dirname,'unrestricted'),from=Number(process.argv[2]),end=Number(process.argv[3]);
const four=JSON.parse(fs.readFileSync(path.join(dir,'updated-four-29-8.json'),'utf8'));
const needed=new Set(four.viable.filter(r=>from<=r.id&&r.id<end).flatMap(r=>r.paths.map(p=>[r.id,...p].join(','))));
const read=f=>{const v=fs.readFileSync(path.join(dir,f),'utf8');return v.slice(0,v.lastIndexOf('\n')+1).trim().split('\n').filter(Boolean).map(JSON.parse);};
const out='updated-five-29-8-'+from+'-'+end+'.jsonl';
for(const r of (fs.existsSync(path.join(dir,out))?read(out):[]))needed.delete([r.id,r.i,r.j].join(','));
for(const f of fs.readdirSync(dir).filter(x=>x.startsWith('early-five-29-8-'))){
  for(const r of read(f)){
    if(!needed.delete([r.id,r.i,r.j].join(',')))continue;
    const {gs,ps}=prefixes[r.id],a=getArms(gs),q=[a[r.i],a[r.j]],xs=[...gs,join(...q)],ys=[...ps,q],b=getArms(xs),live=[];
    for(const [k,l,m] of r.live){
      const p=[b[k],b[l]];
      if(bounds([...xs,join(...p)],[...ys,p],[8],true)[8]<=8)live.push([k,l,m]);
    }
    fs.appendFileSync(path.join(dir,out),JSON.stringify({id:r.id,i:r.i,j:r.j,initial:r.live.length,live})+'\n');
  }
}
