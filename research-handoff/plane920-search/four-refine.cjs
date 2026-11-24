const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const {test}=require('./local-exact.cjs'),prior=require('./four-quadrilateral-probe.json');
const refs=[2,3,4,5].map(i=>require('./four-ops-'+i+'.json'));
const rows=[...new Set(refs.flatMap(r=>r.rows))];
const fn=path.join(__dirname,'four-refined.json');
const records=fs.existsSync(fn)?JSON.parse(fs.readFileSync(fn,'utf8')).records:[];
const limit=Number(process.argv[2]||60000),maxMs=Number(process.argv[3]||65000);
const subset=refs.flatMap(e=>e.results).filter(r=>r.status!=='UNSAT'&&!records.some(h=>h.ops===r.ops&&h.status==='UNSAT'));
const start=Date.now();
for(const s of subset){
 if(Date.now()-start>maxMs)break;
 const r=test(prior.ids,11,{ops:s.ops,rows,sensitivity:true,order:true,live:false,core:process.argv.includes('--core'),conflicts:limit,ms:12000});
 const sha=crypto.createHash('sha256').update(fs.readFileSync(path.join(__dirname,'partial-0-1-2-4-11.cnf'))).digest('hex');
 records.push({ops:s.ops,limit,core:process.argv.includes('--core'),status:r.status,ms:r.ms,cnfSha256:sha,bad:r.bad?.length});
 if(r.status==='SAT'&&!r.bad.length){console.log('Witness',r);break;}
 fs.writeFileSync(fn,JSON.stringify({rows,records},null,2)+'\n');
}
const base=refs.flatMap(e=>e.results).filter(r=>r.status==='UNSAT'),solved=new Set([...base,...records.filter(r=>r.status==='UNSAT')].map(r=>r.ops));
console.log({initial:base.length,finished:solved.size,remaining:112-solved.size,rows:rows.length+20,ms:Date.now()-start});
