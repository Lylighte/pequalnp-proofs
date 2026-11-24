'use strict';
const fs=require('node:fs'),path=require('node:path');
const {prefixes}=require('./three-prefix-all.cjs'),{getArms,join}=require('./unrestricted-prefix.cjs');
const {bounds}=require('./early-fold.cjs');
const dir=path.join(__dirname,'unrestricted');
const viable=[],three=new Set();let visited=0,original=0;
for(const f of fs.readdirSync(dir).filter(n=>n.startsWith('early-four-29-8-'))){
  for(const r of fs.readFileSync(path.join(dir,f),'utf8').trim().split('\n').map(JSON.parse)){
    visited++;original+=r.live.length;
    if(!r.live.length)continue;
    const {gs,ps}=prefixes[r.id];
    if(bounds(gs,ps,[8],true)[8]>8)continue;
    three.add(r.id);
    const opts=getArms(gs),paths=[];
    for(const [i,j] of r.live){
      const pair=[opts[i],opts[j]];
      if(bounds([...gs,join(...pair)],[...ps,pair],[8],true)[8]<=8)paths.push([i,j]);
    }
    if(paths.length)viable.push({id:r.id,paths});
  }
}
const result={visited,original,nonemptyThree:three.size,nonemptyFour:viable.length,count:viable.reduce((s,v)=>s+v.paths.length,0),viable};
if(visited!==3370||original!==3812)throw Error('incomplete fourth level');
fs.writeFileSync(path.join(dir,'updated-four-29-8.json'),JSON.stringify(result)+'\n');
console.log(visited,original,result.nonemptyThree,result.nonemptyFour,result.count);
