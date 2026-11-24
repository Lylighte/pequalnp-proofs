const fs=require('node:fs'),path=require('node:path'),zlib=require('node:zlib'),assert=require('node:assert/strict');
const {runPrefix}=require('./surplus-fifth.cjs'),forest=require('../plane920-core/or-forest-five.json'),earlier=require('./surplus-and-shapes.json').live;
const zero=n=>Array(n).fill(0),scope=a=>a.terms.reduce((m,v)=>m|v,0);
function feasible(I,signatures){
 const sel=signatures.map((v,i)=>I&1<<i?v:0),edges=[];
 for(let i=0;i<sel.length;i++)for(let j=0;j<i;j++)if(sel[i]&sel[j])edges.push([i,j]);
 if(edges.length<2)return true;
 for(const hub of edges[0]){
   if(edges.every(([a,b])=>{
     const l=a===hub?b:b===hub?a:-1;
     return l>=0 && (sel[hub]&sel[l])===sel[l];
   }))return true;
 }
 return false;
}
const counts=zero(6),byPrefix={},keep=[],pre=zero(4),sets=zero(4),known=zero(4),max={},nPF=0;
for(const f of forest.prefixes){
 let late=0,allLevels=0,early=[];
 const num=runPrefix(f,({orbit,number,pairs,ors,e})=>{
   const scopes=ors.map(scope);
   if(number===0)for(let j=0;j<4;j++){
     early[j]=earlier[orbit].byLevel[j].filter(({I})=>feasible(I,scopes.slice(0,j+1)));
     if(early[j].length)pre[j]++;
     sets[j]+=early[j].length;known[j]+=earlier[orbit].byLevel[j].length;
   }
   const sig=[...scopes,scope(e)],live=pairs.filter(([I])=>feasible(I,sig));
   if(live.length){
     late++;counts[4]+=live.length;keep.push([orbit,number,live]);
     const k=Math.max(...live.map(([,m])=>m.toString(2).replaceAll('0','').length));max[k]=(max[k]||0)+1;
   }
   if(live.length||early.some(x=>x.length))allLevels++;
 });
 byPrefix[f.orbit]={num,late,allLevels,early};
 counts[0]+=num;counts[1]+=late;counts[2]+=allLevels;if(late)counts[3]++;
}
const summary={count:counts[0],late:counts[1],any:counts[2],latePrefixes:counts[3],lateCandidates:counts[4],max,earlyPrefixes:pre,earlyI:sets,priorI:known};
fs.writeFileSync(path.join(__dirname,'surplus-shared-scope.json'),JSON.stringify({summary,byPrefix})+'\n');
fs.writeFileSync(path.join(__dirname,'surplus-shared-live.json.gz'),zlib.gzipSync(Buffer.from(JSON.stringify(keep))));
console.log(summary);
