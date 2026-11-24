const fs=require('node:fs'),path=require('node:path');
const {test,allLines}=require('./local-exact.cjs');
const ids=process.argv[2].split(',').map(Number),budget=Number(process.argv[3]),c=Number(process.argv[4]||30000);
const rows=[],runs=[];
for(let i=0;i<8;i++){
 const r=test(ids,budget,{requireTwoOr:true,order:true,sensitivity:true,live:true,swaps:false,rows,conflicts:c,ms:15000});
 runs.push({...r,bad:r.bad?.length});console.log([ids,budget,i,r.status,r.ms,r.rows,r.bad?.length]);
 if(r.status!=='SAT'||!r.bad.length)break;
 rows.push(...r.bad.filter(x=>!rows.includes(x)).slice(0,8));
}
fs.writeFileSync(path.join(__dirname,'cegis-'+ids.join('-')+'-'+budget+'.json'),JSON.stringify({ids,budget,c,rows,runs},null,2)+'\n');
