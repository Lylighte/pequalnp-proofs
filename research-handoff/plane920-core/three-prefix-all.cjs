'use strict';
const fs=require('node:fs'),path=require('node:path'),{perm,apply}=require('../plane920-math/plane-orbits.js');
const {extend}=require('./tree-extension.cjs'),{search}=require('./effective-cut.cjs');
const first=[[1,2]],ps1=[[[1],[2]]],st=perm.filter(p=>apply(3,p)===3),prefixes=[];
extend(first,st,(g2,p2,s2,n2,i,j)=>{
  const xs=[...first,g2],ys=[...ps1,p2];
  extend(xs,s2,(g3,p3,s3,n3,k,l)=>prefixes.push({gs:[...xs,g3],ps:[...ys,p3],st:s3,mult:78*n2*n3,coords:[i,j,k,l]}));
});
const dir=path.join(__dirname,'unrestricted');
if(require.main===module){
const total=Number(process.argv[2]||29),hh=(process.argv[3]||'3,4,5').split(',').map(Number),from=Number(process.argv[4]||0),end=Math.min(prefixes.length,Number(process.argv[5]||prefixes.length));
const out=path.join(dir,'all-three-'+[total,hh.join(''),from,end].join('-')+'.jsonl');
const done=new Set((fs.existsSync(out)?fs.readFileSync(out,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).id));
for(let id=from;id<end;id++){
 if(done.has(id))continue;const r=prefixes[id],live=[],capped=[];
 for(const h of hh){const v=search(r.gs,r.ps,total-13-h,h-3,3000,true);if(v.open)live.push(h);if(v.capped)capped.push(h);}
 fs.appendFileSync(out,JSON.stringify({id,coords:r.coords,mult:r.mult,live,capped})+'\n');
}
console.log(prefixes.length,from,end);
}
module.exports={prefixes};

