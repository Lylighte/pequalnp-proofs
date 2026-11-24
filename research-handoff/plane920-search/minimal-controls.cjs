const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),cp=require('node:child_process');
const {test}=require('./local-exact.cjs'),{check}=require('./check-rup.cjs');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const results=[];
for(const [ids,name] of [[[0,1,2],'triangle'],[[0,1,5],'concurrent']]){
 const rows=require('./cegis-'+ids.join('-')+'-8.json').rows;
 const r=test(ids,8,{order:true,live:false,requireTwoOr:false,sensitivity:false,rows,conflicts:300000,ms:10000});
 assert.equal(r.status,'UNSAT');
 const cnf='control-'+name+'.cnf',proof='control-'+name+'.lrat';
 fs.copyFileSync(path.join(__dirname,'partial-'+ids.join('-')+'-8.cnf'),path.join(__dirname,cnf));
 const p=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',cnf,proof],{cwd:__dirname,windowsHide:true,timeout:10000});
 assert.equal(p.status,20);const certificate=check(cnf,proof);results.push({ids,n:8,rows,solver:r,certificate});
 console.log(name,r.ms,certificate.adds,certificate.empty);
}
fs.writeFileSync(path.join(__dirname,'three-line-controls.json'),JSON.stringify(results,null,2)+'\n');
