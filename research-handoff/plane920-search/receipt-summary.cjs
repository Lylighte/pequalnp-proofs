const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const read=x=>JSON.parse(fs.readFileSync(path.join(__dirname,x),'utf8'));
const summary={scope:'Concrete DIMACS UNSAT; the semantic CNF bridge and the local combinatorial reductions are written mathematically, without a Lean proof.',groups:[]};
for(const [kind,file] of [['quad','quadrilateral-complete.json'],['transverse','three-concurrent-plus-fourth-complete.json']]){
 const manifest=read(file),rec=read('replay/'+kind+'-receipts.json');
 const by=new Map(manifest.complete.map(x=>[x.ops,x.sha256]));
 const c=rec.certificates;assert.equal(new Set(c.map(x=>x.ops)).size,c.length);
 for(const p of c){assert.equal(p.cnfSha256,by.get(p.ops));assert.equal(p.empty,true);}
 const text=c.slice().sort((a,b)=>a.ops-b.ops).map(p=>[p.ops,p.cnfSha256,p.proofSha256].join(' ')).join('\n')+'\n';
 summary.groups.push({kind,ids:manifest.ids,certified:c.length,expected:by.size,
   checkedEmptyClauses:c.length,addedClauses:c.reduce((s,p)=>s+p.add,0),streamBytes:c.reduce((s,p)=>s+p.proofBytes,0),
   storedCompressedBytes:c.reduce((s,p)=>s+(p.archivedBytes||0),0),
   solverMs:c.reduce((s,p)=>s+p.solveMs,0),checkerMs:c.reduce((s,p)=>s+p.checkMs,0),
   certificateDigest:crypto.createHash('sha256').update(text).digest('hex'),failed:rec.attempts.length});
}
fs.writeFileSync(path.join(__dirname,'replay','summary.json'),JSON.stringify(summary,null,2)+'\n');
console.log(summary.groups);
