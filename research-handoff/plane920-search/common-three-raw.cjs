const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),cp=require('node:child_process'),zlib=require('node:zlib'),crypto=require('node:crypto');
const {encode,rows,verify,code}=require('./common-two.cjs'),{checkProof}=require('./stream-rup.cjs');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe'),dir=path.join(__dirname,'common-three-raw');fs.mkdirSync(dir,{recursive:true});
const file=path.join(dir,'summary.json'),res=fs.existsSync(file)?JSON.parse(fs.readFileSync(file)):{cases:{}};
const reps=new Map();
for(let a=0;a<3;a++)for(let b=0;b<3;b++)for(let c=0;c<3;c++)for(let d=0;d<3;d++){
 let key='9999';
 for(const lr of [0,1])for(const flip of [0,1])for(const x of [0,1])for(const y of [0,1]){
   const m=(i,j)=>i&&j?3-i:i;let pairs=[[m(a,x),m(b,x)],[m(c,y),m(d,y)]];
   if(lr)pairs=pairs.map(p=>p.reverse());if(flip)pairs.reverse();
   const k=pairs.flat().join('');if(k<key)key=k;
 }
 reps.set(key,1+(reps.get(key)||0));
}
(async()=>{
 const all=rows(9),start=Date.now(),limit=Number(process.argv[2]||65000);
 for(const [key,weight] of reps){
   if(Date.now()-start>limit)break;
   if(res.cases[key]?.status==='UNSAT')continue;
   const [a,b,c,d]=key.split('').map(Number),pins=[[a,c+3],[b,d+3]],inst=encode(9,4,[0,0,0],[],all,true,'three',pins);
   const cnf=path.join(dir,'temp.cnf'),pf=path.join(dir,'temp.lrat');fs.writeFileSync(cnf,inst.dimacs);
   const sol=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',cnf,pf],{encoding:'utf8',windowsHide:true,timeout:7500});
   const rec={key,weight,status:sol.status===20?'UNSAT':sol.status===10?'SAT':'UNKNOWN'};
   if(sol.status===20){
     const verified=await checkProof(inst.dimacs,pf),z=zlib.gzipSync(fs.readFileSync(pf));
     fs.writeFileSync(path.join(dir,key+'.lrat.gz'),z);Object.assign(rec,verified,{compressed:z.length,cnf:crypto.createHash('sha256').update(inst.dimacs).digest('hex')});
   }
   if(sol.status===10){rec.model=code(sol.stdout,inst);assert.equal(verify(rec.model,9,[0,0,0],[],all).length,0);}
   res.cases[key]=rec;fs.writeFileSync(file,JSON.stringify(res)+'\n');
 }
 console.log({reps:reps.size,status:Object.values(res.cases).reduce((o,r)=>(o[r.status]=(o[r.status]||0)+1,o),{}),ms:Date.now()-start});
})().catch(e=>{console.error(e);process.exitCode=1;});
