'use strict';
const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),zlib=require('node:zlib'),{pipeline}=require('node:stream/promises'),assert=require('node:assert/strict');
const {lines,group}=require('./plane-symmetry.cjs'),{encode}=require('./slice-encode.cjs'),{checkProof}=require('../plane920-search/stream-rup.cjs');
const dir=path.join(__dirname,'slice-runs'),hash=s=>crypto.createHash('sha256').update(s).digest('hex');
async function main(){
 const stats=[];
 for(const [n,k] of [[8,4],[9,4]]){
  const file=JSON.parse(fs.readFileSync(path.join(dir,n+'-'+k+'.json'),'utf8'));
  const covered=new Set(), run=[];
  for(const entry of file.cases){
   const {u}=entry;
   const points=Array.from({length:13},(_,i)=>i).filter(i=>u&(1<<i));
   assert.equal(points.length,n);
   const orbit=new Set(group.map(perm=>points.reduce((m,x)=>m|1<<perm[x],0)));
   for(const value of orbit){assert(!covered.has(value));covered.add(value);}
   assert.equal(orbit.size,entry.orbitSize);assert.equal(entry.verdict,'UNSAT-replayed');
   const regenerated=encode(u,k),fn=path.join(dir,n+'-'+k+'-'+u+'.cnf');
   assert.equal(hash(regenerated),entry.sha256);assert.equal(hash(fs.readFileSync(fn)),entry.sha256);
   const packed=fn+'.lrat.gz', tmp=fn+'.audit-'+process.pid+'.lrat';
   try{
    await pipeline(fs.createReadStream(packed),zlib.createGunzip(),fs.createWriteStream(tmp,{flags:'wx'}));
    const check=await checkProof(regenerated,tmp);assert(check.empty);assert.equal(check.add,entry.add);
    const digest=hash(fs.readFileSync(tmp));run.push({u,orbit:orbit.size,clauses:check.add,digest,cnf:entry.sha256});
   } finally {if(fs.existsSync(tmp))fs.unlinkSync(tmp);}
  }
  const expected=Array.from({length:8192},(_,i)=>i).filter(i=>i.toString(2).replaceAll('0','').length===n);
  assert(expected.every(m=>covered.has(m)));assert.equal(covered.size,expected.length);
  stats.push({n,k,coverage:covered.size,cases:run});console.log(n,k,covered.size,run.reduce((s,r)=>s+r.clauses,0));
 }
 fs.writeFileSync(path.join(dir,'audited-small-slices.json'),JSON.stringify(stats,null,2));
}
main().catch(e=>{console.error(e);process.exitCode=1});
