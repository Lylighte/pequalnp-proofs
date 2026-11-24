const {model,test}=require('./local-exact.cjs'),fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),assert=require('node:assert/strict');
const ids=[0,1,2,4],from=[2,3,4,5].map(k=>require('./four-ops-'+k+'.json')),ref=require('./four-refined.json');
const done=new Map();
function record(q,rows,core){
 const r=model(ids,11,{ops:q.ops,rows,core,live:false,order:true,sensitivity:true});
 const sha=crypto.createHash('sha256').update('p cnf '+r.vars+' '+r.cnf.length+'\n'+r.cnf.map(c=>c.join(' ')+' 0').join('\n')+'\n').digest('hex');
 if(q.cnfSha256)assert.equal(sha,q.cnfSha256);
 assert.ok(!done.has(q.ops));done.set(q.ops,{ops:q.ops,core,rows:rows.slice(),clauses:r.cnf.length,ms:q.ms,sha256:sha});
}
for(const group of from)for(const q of group.results)if(q.status==='UNSAT')record(q,group.rows.slice(0,q.rows-20),false);
for(const q of ref.records)if(q.status==='UNSAT'&&!done.has(q.ops))record(q,ref.rows,!!q.core);
assert.equal(done.size,112);
const good=test(ids,12,{order:true,live:true,sensitivity:true,swaps:true,conflicts:125000,ms:9000});
assert.equal(good.status,'SAT');assert.equal(good.bad.length,0);
fs.writeFileSync(path.join(__dirname,'quadrilateral-complete.json'),JSON.stringify({ids,budget:11,complete:[...done.values()].sort((a,b)=>a.ops-b.ops),positiveControl:good})+'\n');
console.log({complete:done.size,positiveControl:good.status,failedRows:good.bad.length,controlMs:good.ms});
