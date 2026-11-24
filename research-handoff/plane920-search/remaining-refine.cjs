const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const {test,model}=require('./local-exact.cjs');
const base=require('./remaining-four.json'),file=path.join(__dirname,'remaining-refined.json');
const prev=fs.existsSync(file)?JSON.parse(fs.readFileSync(file,'utf8')):{rows:base.rows.slice(),records:[]};
const limit=Number(process.argv[2]||60000),cap=Number(process.argv[3]||75000),start=Date.now();
const done=new Set([...base.records,...prev.records].filter(r=>r.status==='UNSAT').map(r=>r.ops));
for(const e of base.records){
 if(e.ops===null||done.has(e.ops)||Date.now()-start>=cap)continue;
 const opts={ops:e.ops,order:true,core:true,privateBound:true,sensitivity:true,requireTwoOr:true,live:false,rows:prev.rows,conflicts:limit,ms:9000};
 const r=test(base.ids,11,opts),record={ops:e.ops,rows:prev.rows.slice(),status:r.status,ms:r.ms,bad:r.bad?.length,limit};
 if(r.status==='UNSAT')done.add(e.ops);
 else if(r.status==='SAT'){assert(r.bad.length);prev.rows.push(...r.bad.filter(v=>!prev.rows.includes(v)).slice(0,7));}
 prev.records.push(record);fs.writeFileSync(file,JSON.stringify(prev,null,2)+'\n');
}
if(done.size===112){
 const best=new Map([...base.records,...prev.records].filter(r=>r.status==='UNSAT').map(r=>[r.ops,r]));
 const hashes=[];for(const [ops,r] of best){
   const m=model(base.ids,11,{ops,rows:r.rows,order:true,core:true,privateBound:true,sensitivity:true,requireTwoOr:true});
   const text='p cnf '+m.vars+' '+m.cnf.length+'\n'+m.cnf.map(a=>a.join(' ')+' 0').join('\n')+'\n';
   hashes.push({...r,clauses:m.cnf.length,sha256:crypto.createHash('sha256').update(text).digest('hex')});
 }
 fs.writeFileSync(path.join(__dirname,'three-concurrent-plus-fourth-complete.json'),JSON.stringify({ids:base.ids,complete:hashes})+'\n');
}
console.log({done:done.size,remaining:112-done.size,ms:Date.now()-start});
