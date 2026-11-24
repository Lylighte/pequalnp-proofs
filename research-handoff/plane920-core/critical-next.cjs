'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {perm,apply}=require('../plane920-math/plane-orbits.js'),{extend}=require('./tree-extension.cjs');
const {allowed}=require('./wide-prefix.cjs'),{record,getArms,join,signature}=require('./unrestricted-prefix.cjs');
const {search}=require('./effective-cut.cjs');
const dir=path.join(__dirname,'unrestricted'),mapped=(a,p)=>a.map(t=>apply(t,p)).sort((a,b)=>a-b).toString();
const firstStab=new Map();
function stabilizer(pairs){
 const first=pairs[0],xy=first[0][0]|first[1][0];
 if(!firstStab.has(xy))firstStab.set(xy,perm.filter(p=>apply(xy,p)===xy));
 return firstStab.get(xy).filter(p=>pairs.slice(1).every(([a,b])=>{
   const x=mapped(a,p),y=mapped(b,p);return (x===a.toString()&&y===b.toString())||(x===b.toString()&&y===a.toString());}));
}
function restore(id,trail){
 const {gates,pairs}=record(id),gs=gates.slice(),ps=pairs.slice();
 for(let k=0;k<trail.length;k+=2){const choices=getArms(gs),pair=[choices[trail[k]],choices[trail[k+1]]];gs.push(join(...pair));ps.push(pair);}
 return {gs,ps};
}
function runOne(id,trail,cap){
 const {gs,ps}=restore(id,trail),stab=stabilizer(ps);const r={id,trail,stab:stab.length,all:0,eligible:0,tested:0,capped:0,live:[]};
 if(!allowed(gs,ps,true)){r.rejected=true;return r;}
 extend(gs,stab,(g,pair,sub,m,i,j)=>{
   r.all+=m;const os=[...gs,g],arms=[...ps,pair];if(!allowed(os,arms,true))return;
   r.eligible+=m;r.tested++;
   const v=search(os,arms,7,8-os.length,cap,true);
   if(v.capped)r.capped++;if(v.open)r.live.push([i,j,m]);
 });
 return r;
}
module.exports={runOne,restore,stabilizer};
if(require.main===module){
 const from=Number(process.argv[2]||0),end=Number(process.argv[3]||1217),cap=Number(process.argv[4]||8000);
 const file=path.join(dir,'critical-fifth-'+[from,end,cap].join('-')+'.jsonl'),done=new Set((fs.existsSync(file)?fs.readFileSync(file,'utf8'):'').trim().split('\n').filter(Boolean).map(x=>JSON.parse(x).id));
 for(let id=from;id<end;id++)if(!done.has(id))fs.appendFileSync(file,JSON.stringify(runOne(id,[],cap))+'\n');
}

