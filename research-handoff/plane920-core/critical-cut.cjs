'use strict';
const fs=require('node:fs'),path=require('node:path'),{record}=require('./unrestricted-prefix.cjs'),{search}=require('./effective-cut.cjs');
const d=path.join(__dirname,'unrestricted'),total=Number(process.argv[2]),h=Number(process.argv[3]),from=Number(process.argv[4]||0),end=Number(process.argv[5]||1217);
const file=path.join(d,'critical-effective-'+[total,h,from,end].join('-')+'.jsonl');
const done=new Set((fs.existsSync(file)?fs.readFileSync(file,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).id));
for(let id=from;id<end;id++){
  if(done.has(id))continue;const {gates,pairs}=record(id);
  const result=search(gates,pairs,total-13-h,h-4,100000);
  fs.appendFileSync(file,JSON.stringify({id,...result})+'\n');
}

