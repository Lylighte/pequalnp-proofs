const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),cp=require('node:child_process'),zlib=require('node:zlib'),crypto=require('node:crypto');
const {encode,rows}=require('./common-two.cjs'),{checkProof}=require('./stream-rup.cjs');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const dir=path.join(__dirname,'common-two-lower'),data=require('./common-two-lower/results.json'),tally=path.join(dir,'receipts.json');
const res=fs.existsSync(tally)?JSON.parse(fs.readFileSync(tally)):{yes:{},pending:{}};
const patterns=new Set();
for(let a=0;a<5;a++)for(let b=0;b<5;b++)for(let c=0;c<10;c++)for(let d=0;d<10;d++){
 if(a===b&&a>0||c===d&&c>=4)continue;patterns.add([...([a,b].sort((i,j)=>i-j)),...([c,d].sort((i,j)=>i-j))].join(','));
}
assert.equal(patterns.size,539);
const hard='0,0,3,3',keys=[hard,...[...patterns].filter(k=>k!==hard)];
const start=Date.now(),budget=Number(process.argv[2]||50000);
(async()=>{
 for(const key of keys){
  if(Date.now()-start>budget)break;
  if(res.yes[key])continue;
  const p=key.split(',').map(Number),hardest=key===hard;
  const rs=hardest?rows(12):data.rows.slice(0,data.cases[key]?.rows||data.rows.length);
  const {dimacs}=encode(12,4,p.slice(0,2),p.slice(2),rs,true,hardest);
  const cnf=path.join(dir,'proof-active.cnf'),pf=path.join(dir,'proof-active.lrat');fs.writeFileSync(cnf,dimacs);
  const q=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',cnf,pf],{encoding:'utf8',timeout:hardest?12000:3000,windowsHide:true});
  if(q.status===20){
    const verified=await checkProof(dimacs,pf),gz=zlib.gzipSync(fs.readFileSync(pf)),name=p.join('')+'.lrat.gz';
    fs.writeFileSync(path.join(dir,name),gz);res.yes[key]={name,rows:rs.length,bytes:gz.length,sha256:crypto.createHash('sha256').update(dimacs).digest('hex'),...verified};delete res.pending[key];
  }else{res.pending[key]={status:q.status,error:q.error?.code};}
  fs.writeFileSync(tally,JSON.stringify(res)+'\n');
 }
 const r=Object.values(res.yes);console.log({verified:r.length,pending:res.pending,adds:r.reduce((s,a)=>s+a.add,0),bytes:r.reduce((s,a)=>s+a.bytes,0),ms:Date.now()-start});
})().catch(e=>{console.error(e);process.exitCode=1;});
