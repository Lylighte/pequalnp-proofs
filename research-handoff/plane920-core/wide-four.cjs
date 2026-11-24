'use strict';
const fs=require('node:fs'),path=require('node:path'),{roots,allowed}=require('./wide-prefix.cjs');
const {extend}=require('./tree-extension.cjs'),{search}=require('./effective-cut.cjs'),{signature}=require('./unrestricted-prefix.cjs');
const dir=path.join(__dirname,'unrestricted');
const from=Number(process.argv[2]||0),end=Math.min(roots.length,Number(process.argv[3]||roots.length)),cap=Number(process.argv[4]||3000);
const file=path.join(dir,'wide-four-'+[from,end,cap].join('-')+'.jsonl');
const done=new Set((fs.existsSync(file)?fs.readFileSync(file,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).id));
for(let id=from;id<end;id++){
  if(done.has(id))continue;const r=roots[id],live=[];let all=0,possible=0,closed=0;
  extend(r.gs,r.stab,(g,pair,st,m,i,j)=>{
    all++;const gs=[...r.gs,g],ps=[...r.ps,pair];if(!allowed(gs,ps))return;possible++;
    const res=search(gs,ps,7,4,cap);
    if(res.open)live.push([i,j,m,res.capped]);else closed++;
  });
  fs.appendFileSync(file,JSON.stringify({id,all,possible,closed,live})+'\n');
}

