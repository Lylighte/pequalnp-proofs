const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {perm,apply}=require('../plane920-math/plane-orbits.js'),{lines,pc,table}=require('./three-or-five-lines.cjs');
const sets=require('./three-line-five-cores.json');
const domain=Array.from({length:8192},(_,i)=>i).filter(i=>pc[i]<=4),ids=new Map(),all=[],index=[],seen=new Set();
function name(t){const k=t.slice().sort((a,b)=>a-b).join(',');if(!ids.has(k))ids.set(k,ids.size);return ids.get(k);}
function minimal(bits){
 const w=BigInt('0x'+bits),selected=new Set(domain.filter((_,i)=>w&1n<<BigInt(i)));
 return [...selected].filter(x=>{for(let y=x;y;y&=y-1)if(selected.has(x^(y&-y)))return false;return true;});
}
for(let c=0;c<sets.length;c++)for(let h=0;h<sets[c].out.length;h++){
 const source=sets[c],terms=source.out[h].map(minimal),ot=[source.row.firstOr,source.row.t];
 for(let j=0;j<perm.length;j++){
  const p=perm[j],H=terms.map(t=>name(t.map(x=>apply(x,p)))).sort((a,b)=>a-b),O=ot.map(t=>name(t.map(x=>apply(x,p)))).sort((a,b)=>a-b);
  const M=lines.slice(0,3).reduce((m,L)=>m|1<<lines.indexOf(apply(L,p)),0),key=[M,H.join(','),O.join(',')].join('/');
  if(seen.has(key))continue;seen.add(key);const k=all.length;all.push({M,H,O,c,h,j});
  for(const v of H){index[v]??=[];index[v].push(k);}
 }
}
const best={},witness={};
for(let i=0;i<all.length;i++){
 const x=all[i],compare=new Set(x.H.flatMap(v=>index[v]).filter(j=>j<i));
 for(const j of compare){
  const y=all[j],M=x.M|y.M,n=pc[M];if(n<4)continue;
  const cost=10-x.H.filter(h=>y.H.includes(h)).length,or=4-x.O.filter(h=>y.O.includes(h)).length,key=n+','+or;
  if(!(key in best)||cost<best[key]){best[key]=cost;witness[key]={M,x,y};}
 }
}
fs.writeFileSync(path.join(__dirname,'combine-triangle-cores.json'),JSON.stringify({cores:all.length,best,witness})+'\n');
console.log({cores:all.length,best});
