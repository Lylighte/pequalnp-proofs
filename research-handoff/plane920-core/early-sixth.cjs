'use strict';
const fs=require('node:fs'),path=require('node:path');
const {prefixes}=require('./three-prefix-all.cjs'),{extend}=require('./tree-extension.cjs');
const {stabilizer}=require('./critical-next.cjs'),{getArms,join}=require('./unrestricted-prefix.cjs');
const {bounds}=require('./early-fold.cjs'),{search}=require('./effective-cut.cjs');
const dir=path.join(__dirname,'unrestricted'),h=Number(process.argv[2]),id=Number(process.argv[3]);
const input=fs.readdirSync(dir).filter(f=>f.startsWith('early-five-29-'+h+'-'));
const rows=input.flatMap(f=>fs.readFileSync(path.join(dir,f),'utf8').trim().split('\n').filter(Boolean).map(JSON.parse)).filter(r=>r.id===id);
const results=[];
for(const row of rows)for(const [a,b] of row.live){
  const gs=prefixes[id].gs.slice(),ps=prefixes[id].ps.slice();
  for(const [i,j] of [[row.i,row.j],[a,b]]){
    const choices=getArms(gs),p=[choices[i],choices[j]];ps.push(p);gs.push(join(...p));
  }
  const r={id,path:[row.i,row.j,a,b],labelled:0,orbits:0,fold:0,capped:0,live:[]};
  extend(gs,stabilizer(ps),(g,p,next,m,i,j)=>{
    r.labelled+=m;r.orbits++;
    const xs=[...gs,g],ys=[...ps,p];
    if(bounds(xs,ys,[h])[h]>16-h)return;
    r.fold++;const v=search(xs,ys,16-h,h-6,1500,true);
    if(v.capped)r.capped++;if(v.open)r.live.push([i,j,m]);
  });
  results.push(r);
}
fs.writeFileSync(path.join(dir,'early-six-29-'+h+'-'+id+'.json'),JSON.stringify(results)+'\n');console.log(results.map(r=>[r.orbits,r.fold,r.live.length,r.capped]));
