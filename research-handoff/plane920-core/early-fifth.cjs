'use strict';
const fs=require('node:fs'),path=require('node:path');
const {prefixes}=require('./three-prefix-all.cjs'),{extend}=require('./tree-extension.cjs');
const {bounds}=require('./early-fold.cjs'),{search}=require('./effective-cut.cjs');
const dir=path.join(__dirname,'unrestricted');
const h=Number(process.argv[2]),from=Number(process.argv[3]),end=Number(process.argv[4]),cap=1500;
const tag=h===8?'8':'67',outfile=path.join(dir,'early-five-29-'+[h,from,end,cap].join('-')+'.jsonl');
const read=f=>fs.readFileSync(f,'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
const done=new Set((fs.existsSync(outfile)?read(outfile):[]).map(r=>[r.id,r.i,r.j].join(',')));
for(const name of fs.readdirSync(dir).filter(n=>n.startsWith('early-four-29-'+tag+'-')))for(const parent of read(path.join(dir,name))){
  if(parent.id<from||parent.id>=end)continue;
  const todo=new Set(parent.live.filter(([i,j,m,hs])=>hs.includes(h)&&!done.has([parent.id,i,j].join(','))).map(([i,j])=>[i,j].join(',')));
  if(!todo.size)continue;
  const {gs,ps,st}=prefixes[parent.id];
  extend(gs,st,(g,pair,next,m,i,j)=>{
    if(!todo.delete([i,j].join(',')))return;
    const os=[...gs,g],arms=[...ps,pair],r={id:parent.id,i,j,orbits:0,labelled:0,fold:0,capped:0,live:[]};
    extend(os,next,(v,p,stab,mult,k,l)=>{
      r.orbits++;r.labelled+=mult;
      const xs=[...os,v],ys=[...arms,p];
      if(bounds(xs,ys,[h])[h]>16-h)return;
      r.fold++;
      const z=search(xs,ys,16-h,h-5,cap,true);
      if(z.capped)r.capped++;
      if(z.open)r.live.push([k,l,mult]);
    });
    fs.appendFileSync(outfile,JSON.stringify(r)+'\n');
  });
  if(todo.size)throw Error('Unmatched fourth-gate path');
}
