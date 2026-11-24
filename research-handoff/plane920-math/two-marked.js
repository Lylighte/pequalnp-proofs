"use strict";
const fs=require("node:fs"),cp=require("node:child_process"),path=require("node:path"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const {lines,weight:w}=require("./plane-orbits"),pts=Array.from({length:13},(_,i)=>i),ids=s=>pts.filter(i=>s&(1<<i));
const dir=path.join(__dirname,"small-core","shared-high");
function cnf(pos,p,h,degree=4){
 const u=pos.reduce((m,l)=>m|l),pt=ids(u),ng=[];
 for(let t=u;;t=(t-1)&u){if(!pos.includes(t)&&(w[t]<degree||(w[t]===degree&&(t&p))))ng.push(t);if(t===0)break;}
 const rows=[...pos,...ng.filter(t=>!ng.some(x=>x!==t&&(x&t)===t))],cl=[];let nv=0;
 const v=()=>++nv,nt=a=>typeof a==="boolean"?!a:-a,c=(...z)=>{if(!z.includes(true))cl.push(z.filter(x=>x!==false));};
 const vals=rows.map(r=>pt.map(j=>!!(r&(1<<j))));
 for(let h0=0;h0<h;h0++){
  const sides=[],menus=[];
  for(let side=0;side<2;side++){
   const m=Array.from({length:pt.length+h0},v);menus.push(m);
   sides.push(vals.map(sig=>{const hits=m.flatMap((s,j)=>{const a=sig[j];if(a===false)return [];if(a===true)return [s];const z=v();c(-z,a);c(-z,s);c(z,-a,-s);return [z];});
    const z=v();for(const a of hits)c(-a,z);c(-z,...hits);return z;}));
  }
  let prefix=true;for(let j=pt.length+h0-1;j>=0;j--){const a=menus[0][j],b=menus[1][j],eq=v();c(nt(prefix),-a,b);c(nt(prefix),-a,-b,eq);c(nt(prefix),a,b,eq);prefix=eq;}
  for(let r=0;r<rows.length;r++){const a=sides[0][r],b=sides[1][r],z=v();c(-z,a);c(-z,b);c(z,-a,-b);vals[r].push(z);if(h0===h-1)c(r<pos.length?z:-z);}
 }
 return "p cnf "+nv+" "+cl.length+"\n"+cl.map(z=>z.join(" ")+" 0").join("\n")+"\n";
}
module.exports={cnf};
if(require.main===module)(async()=>{
 const a=lines[0],b=lines[1],p=(a&~b)&-(a&~b),q=(b&~a)&-(b&~a),bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
 for(const [marks,h] of [[p,3],[p|q,3],[p|q,4],[p|q,5]]){
  const stem=path.join(dir,"two-high-"+marks+"-"+h),s=cnf([a,b],marks,h);fs.writeFileSync(stem+".cnf",s);
  const z=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c","100000",stem+".cnf",stem+".lrat"],{encoding:"utf8",windowsHide:true,timeout:12000});
  const verdict=z.status===20?"UNSAT":z.status===10?"SAT":"UNKNOWN",rec={a,b,marks,h,verdict};if(verdict==="UNSAT")rec.check=await checkProof(s,stem+".lrat");
  fs.writeFileSync(stem+".json",JSON.stringify(rec,null,2)+"\n");console.log(rec);
 }
})().catch(e=>{console.error(e);process.exitCode=1;});
