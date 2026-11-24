'use strict';
const fs=require('node:fs'),path=require('node:path'),{roots}=require('./tree-extension.cjs');
const {getArms,join,signature,fixed}=require('./unrestricted-prefix.cjs'),{search}=require('./effective-cut.cjs');
const dir=path.join(__dirname,'unrestricted');
function materialize(pathId){
 const {gs,ps}=roots[pathId[0]],g=gs.slice(),pairs=ps.slice();
 for(let i=1;i<pathId.length;i+=2){
   const arms=getArms(g),p=[arms[pathId[i]],arms[pathId[i+1]]];pairs.push(p);g.push(join(...p));
 }
 return [g,pairs];
}
if(require.main===module){
const tot=Number(process.argv[2]||28),h=Number(process.argv[3]||7),stop=Number(process.argv[4]||5),file=path.join(dir,'tree-'+tot+'-5678-'+stop+'.json');
const candidates=require(file).live.filter(r=>r.ok.includes(h)),from=Number(process.argv[5]||0),end=Math.min(candidates.length,Number(process.argv[6]||candidates.length));
const out=path.join(dir,'tree-cut-'+[tot,h,stop,from,end].join('-')+'.jsonl');
const done=new Set((fs.existsSync(out)?fs.readFileSync(out,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).i));
for(let i=from;i<end;i++){
 if(done.has(i))continue;const r=candidates[i],[gs,ps]=materialize(r.path);
 const res=search(gs,ps,tot-13-h,h-stop,30000);
 fs.appendFileSync(out,JSON.stringify({i,p:r.path,...res})+'\n');
}
console.log('done',candidates.length,from,end);
}
module.exports={materialize};

