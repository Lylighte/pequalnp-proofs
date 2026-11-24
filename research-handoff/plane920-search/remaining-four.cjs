const fs=require('node:fs'),path=require('node:path'),{test,pop}=require('./local-exact.cjs');
const ids=[0,1,2,5],budget=11,rows=[],records=[],start=Date.now();
const opt={order:true,core:true,privateBound:true,sensitivity:true,requireTwoOr:true,live:false,rows};
for(let iteration=0;iteration<2;iteration++){
 const r=test(ids,budget,{...opt,conflicts:45000,ms:5000});
 records.push({ops:null,status:r.status,ms:r.ms,rows:rows.slice(),bad:r.bad?.length});
 if(r.status==='SAT'&&r.bad.length)rows.push(...r.bad.slice(0,12));else break;
}
if(!records.some(r=>r.status==='UNSAT'))for(let m=2;m<=5;m++)for(let ops=0;ops<128;ops++){
 if(pop(ops)!==m)continue;
 const r=test(ids,budget,{...opt,ops,conflicts:12000,ms:2500});
 records.push({ops,status:r.status,ms:r.ms,rows:rows.slice(),bad:r.bad?.length});
 if(r.status==='SAT'){
   if(!r.bad.length){console.log('Witness',r);process.exit(1);}
   rows.push(...r.bad.filter(w=>!rows.includes(w)).slice(0,4));
 }
}
const counts={};for(const r of records.filter(r=>r.ops!==null))counts[r.status]=(counts[r.status]||0)+1;
fs.writeFileSync(path.join(__dirname,'remaining-four.json'),JSON.stringify({ids,rows,records,counts},null,2)+'\n');
console.log({global:records[0],counts,ms:Date.now()-start});
