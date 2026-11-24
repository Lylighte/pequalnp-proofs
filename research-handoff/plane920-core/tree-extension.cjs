'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {perm,apply,lines}=require('../plane920-math/plane-orbits.js');
const {join,signature,can,getArms}=require('./unrestricted-prefix.cjs');
const raw=Array.from({length:13},(_,i)=>[1<<i]),programs=[];
const key=(a,b)=>a>b?String(a)+'/'+String(b):String(b)+'/'+String(a);
const mapped=(g,p)=>g.map(m=>apply(m,p)).sort((a,b)=>a-b).toString();
function make(points,steps){
  if(points.length===1){programs.push(steps);return;}
  for(let i=0;i<points.length;i++)for(let j=0;j<i;j++){
    const rest=points.filter((_,k)=>k!==j&&k!==i);
    make([...rest,13+steps.length],[...steps,[points[j],points[i]]]);
  }
}
for(let l=0;l<13;l++)make([0,1,3,9].map(j=>(l+j)%13),[]);
function terms(program){
  const pool=raw.slice(),gs=[],ps=[];
  for(const [i,j] of program){const pair=[pool[i],pool[j]],g=join(...pair);ps.push(pair);gs.push(g);pool.push(g);}
  return {gs,ps};
}
const prefixKey=(ps,p)=>ps.map(([a,b])=>key(mapped(a,p),mapped(b,p))).join('|');
const id=raw.map((_,i)=>i);
const roots=[],seen=new Set(),actual=new Set(programs.map(p=>prefixKey(terms(p).ps,id)));
assert.equal(actual.size,234);
for(const program of programs){
  const {gs,ps}=terms(program),k=prefixKey(ps,id);if(seen.has(k))continue;
  const orbit=new Set(),stab=[];
  for(const p of perm){const s=prefixKey(ps,p);assert(actual.has(s));orbit.add(s);seen.add(s);if(s===k)stab.push(p);}
  assert.equal(orbit.size*stab.length,5616);roots.push({gs,ps,stab,mult:orbit.size,program});
}
assert.equal(roots.length,2);assert.equal(seen.size,234);
function extend(gs,stab,visit){
  const arms=getArms(gs),names=new Set(gs.map(g=>g.toString())),lookup=new Map(arms.map((a,i)=>[a.toString(),i]));
  const action=stab.map(p=>arms.map(a=>{const j=lookup.get(mapped(a,p));assert.notEqual(j,undefined);return j;}));
  const sig=arms.map(signature),len=arms.length,done=new Uint8Array(len*len);
  let valid=0,represented=0;
  for(let i=0;i<len;i++)for(let j=0;j<i;j++){
    const a=sig[i],b=sig[j];if(!(a.active&~b.active)||!(b.active&~a.active))continue;
    const g=join(arms[i],arms[j]),name=g.toString();if(names.has(name)||name===a.key||name===b.key)continue;
    valid++;const label=i*len+j;if(done[label])continue;
    const imgs=new Set(),fix=[];
    for(let k=0;k<action.length;k++){const x=action[k][i],y=action[k][j],v=Math.max(x,y)*len+Math.min(x,y);
      imgs.add(v);done[v]=1;if(v===label)fix.push(stab[k]);}
    assert.equal(imgs.size*fix.length,stab.length);represented+=imgs.size;
    visit(g,[arms[i],arms[j]],fix,imgs.size,i,j);
  }
  assert.equal(valid,represented);
}
function run(total,counts,stop){
 const dir=path.join(__dirname,'unrestricted'),log=path.join(dir,'tree-'+total+'-'+counts.join('')+'-'+stop+'.json');
 const stats={},live=[];
 function dfs(gs,ps,stab,mult,pathId,hs){
   const n=gs.length,ok=can(gs,ps,hs,total);
   for(const h of hs){
     const k=n+','+h,c=stats[k]||={orbits:0,expanded:0,unresolved:0,labelledUnresolved:0};c.orbits++;c.expanded+=mult;
     if(ok.includes(h)){c.unresolved++;c.labelledUnresolved+=mult;}
   }
   if(!ok.length)return;
   if(n===stop){live.push({path:pathId,ok,mult});return;}
   extend(gs,stab,(g,pair,next,f,i,j)=>dfs([...gs,g],[...ps,pair],next,mult*f,[...pathId,i,j],ok));
 }
 roots.forEach((r,i)=>dfs(r.gs,r.ps,r.stab,r.mult,[i],counts));
 const out={total,counts,stop,roots:roots.map(r=>({program:r.program,orbit:r.mult,stab:r.stab.length})),stats,live};
 fs.writeFileSync(log,JSON.stringify(out)+'\n');console.log(stats);
}
module.exports={roots,extend,terms,run};
if(require.main===module)run(Number(process.argv[2]||28),(process.argv[3]||'5,6').split(',').map(Number),Number(process.argv[4]||4));

