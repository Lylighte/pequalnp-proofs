'use strict';
const fs=require('node:fs'),path=require('node:path'),zlib=require('node:zlib'),crypto=require('node:crypto'),assert=require('node:assert/strict');
const {cnfFor,lines}=require('./two-high-cnf.cjs'),{check}=require('../plane920-search/check-rup.cjs');
const dir=path.join(__dirname,'unrestricted','two-high'),other=path.join(__dirname,'../plane920-search');
const hash=x=>crypto.createHash('sha256').update(x).digest('hex');
const geometry=require('../plane920-math/small-core/high-pairs.json').rr;
const pairs=geometry.flatMap(({a,b})=>[[a,b],[b,a]]);
assert.equal(new Set(pairs.map(x=>x.toString())).size,12);
const results=[];
for(const [a,b] of pairs){
  const stem=path.join(dir,a+'-'+b),old=JSON.parse(fs.readFileSync(stem+'.json','utf8'));
  const expected=[...new Set(lines.flatMap(l=>[l,...lines.map((_,p)=>l&~(1<<p))]))].sort((a,b)=>a-b);
  assert.deepEqual(expected,old.rows);
  const {cnf}=cnfFor(a,b,expected);
  assert.equal(hash(cnf),old.cnf);assert.equal(fs.readFileSync(stem+'.cnf','utf8'),cnf);
  const proof=zlib.gunzipSync(fs.readFileSync(stem+'.lrat.gz')),tmp=stem+'.audit.lrat';
  assert.equal(hash(proof),old.check.proofSha256);fs.writeFileSync(tmp,proof);
  const verified=check(path.relative(other,stem+'.cnf'),path.relative(other,tmp));
  assert.equal(verified.adds,old.check.add);assert(verified.empty);fs.unlinkSync(tmp);
  results.push({a,b,add:verified.adds,vars:verified.vars,clauses:verified.clauses,cnf:old.cnf,proof:hash(proof)});
}
fs.writeFileSync(path.join(dir,'audit.json'),JSON.stringify(results,null,2)+'\n');
console.log('certificates',results.length,'steps',results.reduce((s,r)=>s+r.add,0));

