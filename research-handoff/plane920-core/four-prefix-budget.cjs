'use strict';
const fs=require('node:fs'),path=require('node:path'),{can,record}=require('./unrestricted-prefix.cjs');
const total=Number(process.argv[2]||27),active=(process.argv[3]||'5,6,7,8').split(',').map(Number),result={};
for(const h of active)result[h]=[];
for(let id=0;id<1217;id++){
  const {gates,pairs}=record(id);
  for(const h of can(gates,pairs,active,total))result[h].push(id);
}
fs.writeFileSync(path.join(__dirname,'unrestricted','prefix-'+total+'-'+active.join('')+'.json'),JSON.stringify(result)+'\n');
console.log(Object.fromEntries(active.map(h=>[h,result[h].length])));

