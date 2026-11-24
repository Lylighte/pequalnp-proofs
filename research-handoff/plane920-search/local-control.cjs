const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {test}=require('./local-exact.cjs'),out=[];
for(const ids of [[0,1,2],[0,1,5]]){
 for(const n of [7,8]){
   const rows=require('./cegis-'+ids.join('-')+'-'+n+'.json').rows;
   const r=test(ids,n,{requireTwoOr:false,sensitivity:false,live:true,order:true,rows,conflicts:250000,ms:15000});
   out.push({ids,n,kind:'No sensitivity or OR-count restriction',...r});console.log(ids,n,r.status,r.ms,r.rows);
 }
 const r=test(ids,9,{requireTwoOr:false,order:true,sensitivity:true,live:true,swaps:true,conflicts:250000,ms:18000});
 out.push({ids,n:9,kind:'Known feasible gate budget',...r});console.log(ids,9,r.status,r.ms,r.bad?.length);
}
fs.writeFileSync(path.join(__dirname,'local-control.json'),JSON.stringify(out,null,2)+'\n');
