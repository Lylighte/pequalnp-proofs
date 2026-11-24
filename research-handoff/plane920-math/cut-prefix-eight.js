"use strict";
const fs=require("node:fs"),path=require("node:path"),{record,keys}=require("../plane920-core/unrestricted-prefix.cjs"),{lines,weight:w}=require("./plane-orbits");
const ids=Array.from({length:13},(_,i)=>i),raw=ids.map(i=>[1<<i]);
const masks=Array.from({length:8192},(_,i)=>i).filter(m=>w[m]<=4);
function cutBound(t){return t>=9?7:t>=5?6:t>=3?5:t===2?4:t===1?2:0;}
function inspect(gs,ps){
 const known=new Set(raw.map(keys)),mand=new Map();let excluded=[];
 for(let i=0;i<gs.length;i++){for(const a of ps[i])if(!known.has(keys(a)))mand.set(keys(a),a);known.add(keys(gs[i]));}
 const orig=[...mand.values()];
 const loss=orig.map(a=>lines.reduce((m,l,i)=>m|((a.some(t=>(t&l)===t)&&!a.some(t=>w[t]<=1&&(t&l)===t))?1<<i:0),0));
 if(orig.length<=16)for(let k=1;k<(1<<orig.length);k++){
  let lost=0,dropped=0;for(let i=0;i<orig.length;i++)if(k>>i&1){lost|=loss[i];dropped++;}
  if(8-dropped<cutBound(13-w[lost]))return {count:orig.length,reject:{k,dropped,lost,n:13-w[lost]}};
 }
 for(const cut of masks){
  const L=lines.filter(l=>!(l&cut)),rank=cutBound(L.length),allow=8-rank;
  if(allow>=orig.length)continue;
  const kept=[],skipped=[];
  for(const a of orig){
   const t=a.filter(m=>w[m]<=4&&!(m&cut)),singles=t.filter(m=>w[m]<=1);
   const rawLower=L.every(l=>!t.some(m=>(m&l)===m)||singles.some(m=>(m&l)===m));
   if(rawLower){skipped.push("raw");continue;}
   const k=t.join(",");if(kept.includes(k))skipped.push("equals");else kept.push(k);
  }
  if(skipped.length>allow){excluded.push({cut,n:L.length,count:skipped.length,allow});break;}
 }
 return {count:orig.length,reject:excluded[0]||null};
}
module.exports={inspect};
if(require.main===module){const failed=[],passed=[];for(let i=0;i<1217;i++){const {gates,pairs}=record(i),r=inspect(gates,pairs);if(r.reject)failed.push({i,...r});else passed.push(i);}
fs.writeFileSync(path.join(__dirname,"small-core","cut-prefix-eight.json"),JSON.stringify({failed,passed})+"\n");console.log({failed:failed.length,passed:passed.length});}
