'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {perm,apply}=require('../plane920-math/plane-orbits.js'),{extend}=require('./tree-extension.cjs');
const {join,signature,getArms,fixed,can}=require('./unrestricted-prefix.cjs'),{search}=require('./effective-cut.cjs');
const d=path.join(__dirname,'unrestricted'),pc=n=>n.toString(2).replaceAll('0','').length;
function allowed(gs,ps,strong=false){
  const known=new Set(Array.from({length:13},(_,i)=>(1<<i).toString())),m=new Map();
  for(let i=0;i<gs.length;i++){
    for(const term of ps[i]){
      const a=signature(term);if(!known.has(a.key))m.set(a.key,a.active);
    }
    known.add(gs[i].toString());
  }
  const masks=[...m.values()];
  if(masks.length>7)return false;
  for(let subset=1;subset<(1<<masks.length);subset++){
    let u=0;for(let i=0;i<masks.length;i++)if(subset&(1<<i))u|=masks[i];
    const lost=pc(subset),kept=pc(8191^u);
    if((lost>=1&&kept>=(strong?10:11))||(lost>=2&&kept>=(strong?6:7))||(lost>=3&&kept>=3)||(lost>=4&&kept>=2)||(lost>=6&&kept>=1))return false;
  }
  return true;
}
const first=[[1,2]],firstPair=[[[1],[2]]],stab=perm.filter(p=>apply(3,p)===3);
const roots=[];
extend(first,stab,(g,p,sub,m,i,j)=>{
 const g2=[...first,g],p2=[...firstPair,p];
 if(!allowed(g2,p2))return;
 extend(g2,sub,(g,p,sub,m2,k,l)=>{
   const gs=[...g2,g],ps=[...p2,p];if(allowed(gs,ps))roots.push({gs,ps,stab:sub,mult:78*m*m2,coords:[i,j,k,l]});
 });
});
if(require.main===module){
 const from=Number(process.argv[2]||0),end=Math.min(roots.length,Number(process.argv[3]||roots.length)),test=process.argv.includes('--search');
 const out=path.join(d,'wide-three-'+[from,end,test].join('-')+'.jsonl');
 const done=new Set((fs.existsSync(out)?fs.readFileSync(out,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).id));
 for(let id=from;id<end;id++)if(!done.has(id)){
   const r=roots[id],result=test?search(r.gs,r.ps,7,5,5000):{};
   fs.appendFileSync(out,JSON.stringify({id,mult:r.mult,coords:r.coords,...result})+'\n');
 }
 console.log('representatives',roots.length,'covered',roots.reduce((s,r)=>s+r.mult,0));
}
module.exports={allowed,roots};

