const fs=require('node:fs'),path=require('node:path'),{test,pop}=require('./local-exact.cjs');
const prior=require('./four-quadrilateral-probe.json'),rows=prior.rows.slice(),results=[];
const arg=Number(process.argv[2]||5),limit=Number(process.argv[3]||8000),maxMs=Number(process.argv[4]||60000);
const start=Date.now();
for(let ops=0;ops<128&&Date.now()-start<maxMs;ops++)if(pop(ops)===arg){
 let r;
 for(let repeat=0;repeat<3&&Date.now()-start<maxMs;repeat++){
   r=test(prior.ids,11,{ops,rows,sensitivity:true,order:true,live:false,conflicts:limit,ms:2500});
   if(r.status!=='SAT'||!r.bad.length)break;
   rows.push(...r.bad.filter(w=>!rows.includes(w)).slice(0,4));
 }
 results.push({ops,status:r.status,ms:r.ms,bad:r.bad?.length,rows:r.rows});
 if(r.status==='SAT'&&!r.bad.length){console.log('Witness',r);break;}
}
const counts={};for(const r of results)counts[r.status]=(counts[r.status]||0)+1;
fs.writeFileSync(path.join(__dirname,'four-ops-'+arg+'.json'),JSON.stringify({ids:prior.ids,arg,limit,rows,results,counts},null,2)+'\n');
console.log({orInputs:arg,counts,ms:Date.now()-start});
