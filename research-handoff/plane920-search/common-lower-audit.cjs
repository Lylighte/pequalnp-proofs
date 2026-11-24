const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),crypto=require('node:crypto'),zlib=require('node:zlib');
const {encode,verify,rows}=require('./common-two.cjs'),{checkProof}=require('./stream-rup.cjs');
const r=dir=>path.join(__dirname,dir),standard=r('common-two-lower'),nine=r('common-three-raw'),six=r('common-two-replay');
const proofDb=require('./common-two-lower/receipts.json'),d=require('./common-two-lower/results.json'),nineDb=require('./common-three-raw/summary.json').cases;
const cases=new Set();
for(let a=0;a<=4;a++)for(let b=0;b<=4;b++)for(let c=0;c<10;c++)for(let e=0;e<10;e++){
 if(a===b&&a!==0||c===e&&c>=4)continue;
 cases.add([...([a,b].sort()),...([c,e].sort())].join(','));
}
assert.equal(cases.size,539);assert(cases.delete('0,0,3,3'));
assert.deepEqual(cases,new Set(Object.keys(proofDb.yes)));
const canonical=tuple=>{
 const choices=[];
 for(const t of [tuple,[...tuple].reverse()])for(const [v,w] of [[0,0],[0,1],[1,0],[1,1]])for(const reverse of [false,true]){
   choices.push(t.map((p,g)=>p.map(j=>j&&[v,w][g]?3-j:j)).map(p=>reverse?p.reverse():p).flat().join(''));
 }
 return choices.sort()[0];
};
const orbits=new Map();
for(let v=0;v<81;v++){
 const x=Array.from({length:4},(_,i)=>Math.floor(v/(3**i))%3),k=canonical([x.slice(0,2),x.slice(2)]);
 orbits.set(k,(orbits.get(k)||0)+1);
}
assert.deepEqual(new Set(orbits.keys()),new Set(Object.keys(nineDb)));
const spool=path.join(standard,'audit.lrat');let checks=0,adds=0,bytes=0;
async function replay(dimacs,dir,name,meta){
 const z=fs.readFileSync(path.join(dir,name)),file=zlib.gunzipSync(z);
 if(meta.cnf||meta.sha256)assert.equal(crypto.createHash('sha256').update(dimacs).digest('hex'),meta.cnf||meta.sha256);
 assert.equal(crypto.createHash('sha256').update(file).digest('hex'),meta.proofSha256);
 fs.writeFileSync(spool,file);const check=await checkProof(dimacs,spool);
 assert.equal(check.add,meta.add);checks++;adds+=check.add;bytes+=z.length;
}
(async()=>{
 const start=Date.now(),sixRec=require('./common-two-replay/results.json').find(x=>x.h===3&&x.pat.join()==='0,0');
 await replay(encode(6,3,[0,0],[],rows(6)).dimacs,six,sixRec.name,sixRec);
 for(const key of cases){
   const p=key.split(',').map(Number),rec=proofDb.yes[key];
   await replay(encode(12,4,p.slice(0,2),p.slice(2),d.rows.slice(0,rec.rows),true).dimacs,standard,rec.name,rec);
 }
 for(const [key,weight] of orbits){
   const [a,b,c,e]=key.split('').map(Number),rec=nineDb[key];assert.equal(weight,rec.weight);
   await replay(encode(9,4,[0,0,0],[],rows(9),true,'three',[[a,c+3],[b,e+3]]).dimacs,nine,key+'.lrat.gz',rec);
 }
 fs.unlinkSync(spool);
 const allowed=rows(12);
 for(const m of allowed){
   const A=(m&6)===6,B=(m&40)===40,F=(A||!!(m&16))&&(B||!!(m&1));
   const outputs=[F&&A,F&&B,(m&448)===448,(m&3584)===3584];
   assert.deepEqual(outputs,[7,56,448,3584].map(t=>m===t));
 }
 const out={formalPatternCount:539,directCases:538,threeRawCases:11,sixPointBase:1,proofs:checks,additions:adds,compressedBytes:bytes,controlRows:allowed.length,ms:Date.now()-start};
 fs.writeFileSync(path.join(standard,'audit.json'),JSON.stringify(out,null,2)+'\n');console.log(out);
})().catch(e=>{console.error(e);process.exitCode=1;});
