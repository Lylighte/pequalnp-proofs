"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process"),{lines,weight:w}=require("./plane-orbits"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const ids=Array.from({length:13},(_,i)=>i),rank=Number(process.argv[2]||3),budget=Number(process.argv[3]||150000);
const L=lines[0],p=1,T=L^p,rows=[...new Set([...ids.map(i=>1<<i),...lines,...Array.from({length:8192},(_,i)=>i).filter(r=>w[r]===3||(w[r]===4&&(r&p)))])],at=new Map(rows.map((r,i)=>[r,i]));
const cls=[],vals=rows.map(r=>ids.map(i=>!!(r>>i&1)));let nv=0;const v=()=>++nv,ng=x=>typeof x==="boolean"?!x:-x,c=(...xs)=>{if(!xs.includes(true))cls.push(xs.filter(x=>x!==false));};
for(let g=0;g<rank;g++){
 const sides=[],menus=[];for(let side=0;side<2;side++){
  const m=Array.from({length:13+g},v);menus.push(m);
  sides.push(vals.map(sig=>{const hits=m.flatMap((s,j)=>{const a=sig[j];if(a===false)return [];if(a===true)return [s];const z=v();c(-z,a);c(-z,s);c(z,-a,-s);return [z];});const z=v();for(const x of hits)c(-x,z);c(-z,...hits);return z;}));
 }
 let pref=true;for(let j=13+g-1;j>=0;j--){const a=menus[0][j],b=menus[1][j],z=v();c(ng(pref),-a,b);c(ng(pref),-a,-b,z);c(ng(pref),a,b,z);pref=z;}
 for(let i=0;i<rows.length;i++){
  const row=rows[i],a=sides[0][i],b=sides[1][i],z=g===rank-1?(row===L||row===T?true:rank===4&&lines.includes(row)&&(row&2)?v():false):v();c(ng(z),a);c(ng(z),b);c(z,-a,-b);vals[i].push(z);
 }
}
const novel=Array.from({length:rank},(_,j)=>lines.map(l=>{
 const z=v(),on=vals[at.get(l)][13+j],raw=ids.filter(i=>l>>i&1).map(i=>vals[at.get(1<<i)][13+j]);
 c(-z,on);for(const h of raw)c(-z,ng(h));c(z,ng(on),...raw);return z;
}));
function atLeast(ls,k){
 let old=Array(k+1).fill(false);old[0]=true;
 for(const a of ls){const next=[true];for(let q=1;q<=k;q++){const z=v();c(-z,old[q],a);c(-z,old[q],old[q-1]);next[q]=z;}old=next;}
 c(old[k]);
}
for(let s=1;s<(1<<rank);s++)if(w[s]>=2){const keep=[0,0,5,9,11][w[s]],ports=lines.map((_,i)=>{const z=v(),rs=novel.filter((_,j)=>s>>j&1).map(a=>a[i]);c(-z,...rs);return z;});atLeast(ports,keep);}
const dim="p cnf "+nv+" "+cls.length+"\n"+cls.map(x=>x.join(" ")+" 0").join("\n")+"\n",stem=path.join(__dirname,"small-core","rare-early-"+rank+"-"+budget);
fs.writeFileSync(stem+".cnf",dim);
(async()=>{const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe",z=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(budget),stem+".cnf",stem+".lrat"],{encoding:"utf8",windowsHide:true,timeout:18000}),verdict=z.status===20?"UNSAT":z.status===10?"SAT":"UNKNOWN",o={rank,budget,verdict};if(verdict==="UNSAT")o.check=await checkProof(dim,stem+".lrat");fs.writeFileSync(stem+".json",JSON.stringify(o,null,2)+"\n");console.log(o);})();
