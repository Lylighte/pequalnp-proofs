'use strict';
const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),zlib=require('node:zlib'),assert=require('node:assert/strict');
const dir=path.join(__dirname,'../plane920-search/replay-disjoint-cross');
const rec=JSON.parse(fs.readFileSync(path.join(dir,'receipts.json'),'utf8'));
const hash=t=>crypto.createHash('sha256').update(t).digest('hex');
const summary={cases:0,stored:0,direct:0,compressedBytes:0,clauseAdditions:0};
for(const [key,r] of Object.entries(rec.receipts)){
 summary.cases++;assert(r.empty || r.direct || r.directEmpty || r.add===0,key);
 if(!r.name){summary.direct++;continue;}
 const packed=fs.readFileSync(path.join(dir,r.name));assert.equal(packed.length,r.compressed);
 const proof=zlib.gunzipSync(packed);assert.equal(proof.length,r.proofBytes);
 assert.equal(hash(proof),r.proofSha256);summary.stored++;summary.compressedBytes+=packed.length;summary.clauseAdditions+=r.add;
}
assert.equal(summary.cases,408);assert.equal(summary.stored,407);assert.equal(summary.clauseAdditions,1095002);
fs.writeFileSync(path.join(__dirname,'cross-receipt-audit.json'),JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify(summary));
