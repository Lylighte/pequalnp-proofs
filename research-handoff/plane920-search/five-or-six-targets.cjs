const fs=require('node:fs'),path=require('node:path');
const {perm,apply}=require('../plane920-math/plane-orbits.js');
const {lines,pc,mult,join,orbits}=require('./three-or-five-lines.cjs');
const maps=perm.map(p=>lines.map(L=>lines.indexOf(apply(L,p))));
const seven=process.argv.includes('--seven');
const seen=new Set(),families=[];
for(let m=0;m<8192;m++)if(pc[m]===(seven?7:6)&&!seen.has(m)){
 const gp=[];for(let i=0;i<perm.length;i++){const t=apply(m,maps[i]);seen.add(t);if(t===m)gp.push(perm[i]);}
 families.push({m,gp});
}
function nextT(old,M){
 const pool=new Map(),pre=new Set(old.map(t=>t.join(','))),ops=[[0]];
 for(const t of old)for(const s of [...ops])ops.push(mult(s,t));
 for(let p=-1;p<13;p++)for(let j=0;j<ops.length;j++){
  if(p<0&&!j)continue;const t=p<0?ops[j]:mult([1<<p],ops[j]),k=t.join(',');if(pool.has(k))continue;
  const alive=lines.reduce((m,L,i)=>m|(t.some(s=>(s&L)===s)?1<<i:0),0)&M;
  if(pc[alive]>=2&&(!process.argv.includes('--pay3')||pc[alive]>=3||pre.has(k)||(t.length===1&&pc[t[0]]===1)))pool.set(k,{t,alive});
 }
 const opts=[...pool.values()],unique=new Map();
 for(let i=0;i<opts.length;i++)for(let j=0;j<i;j++){
   const a=opts[i],b=opts[j];if(pc[a.alive&~b.alive]<2||pc[b.alive&~a.alive]<2)continue;
   const t=join(a.t,b.t),k=t.join(',');if(!pre.has(k))unique.set(k,t);
 }
 return unique;
}
function prefixes(M,gp,depth,visit){
 function step(prefix,g){
   if(prefix.length===depth)return visit(prefix,g);
   for(const e of orbits(nextT(prefix,M),g))step([...prefix,e.t],e.stab);
 }
 step([],gp);
}
if(require.main===module){
 const n=Number(process.argv[2]||3),out=[];
 for(const {m,gp} of families){
   let count=0,sampled=0,total=0;
   prefixes(m,gp,n,(t,g)=>{if(count%17===0){sampled++;total+=nextT(t,m).size;}count++;});
   out.push({m,stabilizer:gp.length,depth:n,count,sampled,children:total});console.log(out.at(-1));
 }
 fs.writeFileSync(path.join(__dirname,'five-or-six-target-prefix-'+n+'.json'),JSON.stringify(out)+'\n');
}
module.exports={families,nextT,prefixes};
