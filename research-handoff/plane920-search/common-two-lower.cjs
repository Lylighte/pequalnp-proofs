const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),cp=require('node:child_process');
const {encode,code,verify,rows}=require('./common-two.cjs');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe'),h=4;
const dir=path.join(__dirname,'common-two-lower');fs.mkdirSync(dir,{recursive:true});
const result=path.join(dir,'results.json'),all=rows(12),ts=[7,56,448,3584];
const state=fs.existsSync(result)?JSON.parse(fs.readFileSync(result)):{rows:all.filter(m=>ts.some(t=>(m&t)===m)),cases:{}};
const patterns=[];
for(let a=0;a<=h;a++)for(let b=a;b<=h;b++)if(!a||a!==b)
 for(let c=0;c<10;c++)for(let d=c;d<10;d++)if(c<h||c!==d)patterns.push([a,b,c,d]);
assert.equal(patterns.length,539);
const start=Date.now(),budget=Number(process.argv[2]||30000),timeout=Number(process.argv[3]||850);
for(const p of patterns){
 const key=p.join(',');
 if(state.cases[key]?.status==='UNSAT')continue;
 if(Date.now()-start>=budget)break;
 const exempt=p.slice(0,2),plain=p.slice(2);
 for(let iter=0;iter<6;iter++){
   const inst=encode(12,h,exempt,plain,state.rows),file=path.join(dir,'active.cnf');fs.writeFileSync(file,inst.dimacs);
   const q=cp.spawnSync(solver,['-q','-c','50000',file],{encoding:'utf8',timeout,windowsHide:true});
   if(q.status===20){state.cases[key]={status:'UNSAT',rows:state.rows.length};break;}
   if(q.status!==10){state.cases[key]={status:'UNKNOWN',rows:state.rows.length};break;}
   const model=code(q.stdout,inst),bad=verify(model,12,exempt,plain,all);assert(state.rows.every(m=>!bad.includes(m)));
   if(!bad.length){state.cases[key]={status:'SAT',model};break;}
   state.rows.push(...bad.slice(0,12));
 }
 fs.writeFileSync(result,JSON.stringify(state)+'\n');
 if(state.cases[key]?.status==='SAT')break;
}
console.log({patterns:patterns.length,attempted:Object.keys(state.cases).length,rows:state.rows.length,counts:Object.values(state.cases).reduce((o,e)=>(o[e.status]=(o[e.status]||0)+1,o),{}),ms:Date.now()-start});
