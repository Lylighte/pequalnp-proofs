'use strict';
const fs=require('node:fs'),path=require('node:path');
const {prefixes}=require('./three-prefix-all.cjs'),{extend}=require('./tree-extension.cjs');
const {bounds}=require('./early-fold.cjs'),{search}=require('./effective-cut.cjs');
const dir=path.join(__dirname,'unrestricted');
const hs=process.argv[2].split(',').map(Number),from=Number(process.argv[3]),end=Number(process.argv[4]);
const cap=Number(process.argv[5]||1500),tag=hs.join('');
const file=path.join(dir,'early-four-29-'+[tag,from,end,cap].join('-')+'.jsonl');
const completed=new Set((fs.existsSync(file)?fs.readFileSync(file,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).id));
for(let id=from;id<end;id++){
  if(completed.has(id))continue;
  const {gs,ps,st}=prefixes[id],initial=bounds(gs,ps,hs);
  const eligible=hs.filter(h=>initial[h]<=16-h);
  const counts=Object.fromEntries(hs.map(h=>[h,{fold:0,live:0,capped:0}]));
  const r={id,eligible,orbits:0,labelled:0,counts,live:[]};
  if(eligible.length)extend(gs,st,(g,pair,next,m,i,j)=>{
    r.orbits++;r.labelled+=m;
    const os=[...gs,g],arms=[...ps,pair],f=bounds(os,arms,eligible),open=[];
    for(const h of eligible){
      if(f[h]>16-h)continue;
      const c=counts[h];c.fold++;
      const v=search(os,arms,16-h,h-4,cap,true);
      if(v.open){c.live++;open.push(h);}
      if(v.capped)c.capped++;
    }
    if(open.length)r.live.push([i,j,m,open]);
  });
  fs.appendFileSync(file,JSON.stringify(r)+'\n');
}
