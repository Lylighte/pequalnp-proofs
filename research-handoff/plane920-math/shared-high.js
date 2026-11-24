"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const {lines,weight:w,perm,apply}=require("./plane-orbits"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const all=8191,ix=Array.from({length:13},(_,i)=>i),lm=perm.map(g=>lines.map(l=>lines.indexOf(apply(l,g))));
const ids=m=>ix.filter(i=>m&(1<<i)),both=(l,p)=>(l<<13)|p,dir=path.join(__dirname,"small-core","shared-high");
fs.mkdirSync(dir,{recursive:true});
function triples() {
 const seen=new Set(),recs=[];
 for(let tr=0;tr<=all;tr++)if(w[tr]===3){
  const S=ids(tr);
  function add(j,p){
   if(j<3){
    const l=lines[S[j]],other=S.reduce((m,i)=>m|(i===S[j]?0:lines[i]),0);
    for(const q of ids(l&~other))add(j+1,p|(1<<q));return;
   }
   if(seen.has(both(tr,p)))return;
   const orb=new Set(perm.map((g,i)=>both(apply(tr,lm[i]),apply(p,g))));
   for(const k of orb)seen.add(k);recs.push({tr,p,orbit:orb.size});
  }
  add(0,0);
 }
 return recs;
}
function cnf(tr,p,h) {
 const pos=ids(tr).map(i=>lines[i]),u=pos.reduce((a,b)=>a|b),points=ids(u);
 // Test inclusion-maximal negative assignments only. The output is monotone.
 const neg=[];
 for(let s=u;;s=(s-1)&u){
  if(w[s]<=4&&!pos.includes(s)&&(w[s]<=3||(s&p)))neg.push(s);
  if(!s)break;
 }
 const rows=[...pos,...neg.filter(s=>!neg.some(t=>s!==t&&(s&t)===s)||pos.some(l=>w[s]===3&&(s&l)===s))],positive=new Set(pos);
 const cls=[];let nv=0;const v=()=>++nv,rowsigs=rows.map(s=>points.map(i=>Boolean(s&(1<<i))));
 function c(...xs){if(!xs.includes(true))cls.push(xs.filter(x=>x!==false));}
 function nt(a){return typeof a==="boolean"?!a:-a;}
 const consumers=Array.from({length:h-1},()=>[]);
 for(let g=0;g<h;g++){
  const arms=[],sels=[];
  for(let side=0;side<2;side++){
   const menu=Array.from({length:points.length+g},v);sels.push(menu); for(let j=0;j<g;j++)consumers[j].push(menu[points.length+j]);
      const posHits=pos.map((l,i)=>menu.map((s,j)=>{
    const a=rowsigs[i][j];if(a===false)return false;if(a===true)return s;
    const t=v();c(-t,s);c(-t,a);c(t,-s,-a);return t;
   }));
   for(let j=0;j<menu.length;j++){
    const labs=posHits.map(hits=>{
     if(hits[j]===false)return false;
     const z=v();c(-z,hits[j]);for(let k=0;k<hits.length;k++)if(k!==j)c(-z,nt(hits[k]));return z;
    });c(-menu[j],...labs);
   }
   arms.push(rowsigs.map(sig=>{
    const hits=menu.flatMap((s,j)=>{
     const a=sig[j];if(a===false)return [];if(a===true)return [s];
     const z=v();c(-z,s);c(-z,a);c(z,-s,-a);return [z];
    });
    const t=v();for(const x of hits)c(-x,t);c(-t,...hits);return t;
   }));
  }
  if(g===h-1){
   for(let p=0;p<points.length;p++)c(-sels[0][p]);
   for(let j=0;j<g;j++)c(-sels[0][points.length+j],-sels[1][points.length+j]);
   for(let p=0;p<points.length;p++)c(-sels[0][points.length],-sels[1][p]);
  }
  let pref=true;
  for(let i=(g===h-1?-1:sels[0].length-1);i>=0;i--){const a=sels[0][i],b=sels[1][i],eq=v();c(nt(pref),-a,b);c(nt(pref),-a,-b,eq);c(nt(pref),a,b,eq);pref=eq;}
  for(let r=0;r<rows.length;r++){
   const a=arms[0][r],b=arms[1][r],t=v();rowsigs[r].push(t);c(-t,a);c(-t,b);c(t,-a,-b);
   if(g===h-1)c(positive.has(rows[r])?t:-t);
  }
 }
 for(const xs of consumers)c(...xs);
 const low=Array.from({length:h-1},(_,i)=>points.length+i),at=r=>rowsigs[rows.indexOf(r)];
 for(const s of pos)for(let sub=s;sub;sub=(sub-1)&s){
  const need=w[sub]-2;
  if(need<=0)continue;
  const labels=low.map(slot=>{
   const t=v();c(-t,at(s)[slot]);
   for(const p of ids(sub))c(-t,...ids(sub&~(1<<p)).map(q=>-at(s^(1<<q))[slot]));
   return t;
  });
  for(let m=0;m<(1<<low.length);m++)if(w[m]===low.length-need+1)c(...labels.filter((_,j)=>m&(1<<j)));
 }
 if(h===5){
  for(const slot of low)c(...pos.map(s=>at(s)[slot]));
  for(let i=0;i<3;i++)for(let j=0;j<i;j++)for(const s1 of low)for(const s2 of low)if(s1<s2)c(at(pos[i])[s1],at(pos[i])[s2],at(pos[j])[s1],at(pos[j])[s2]);
 }
 return "p cnf "+nv+" "+cls.length+"\n"+cls.map(x=>x.join(" ")+" 0").join("\n")+"\n";
}
module.exports={triples,cnf};
if(require.main===module)(async()=>{
 const reps=triples(),budget=Number(process.argv[2]||25000),specific=Number(process.argv[3]??-1),h=Number(process.argv[4]||5);
 console.log(reps);
 const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
 for(const [i,r] of reps.entries()){
  if(specific>=0&&i!==specific)continue;
  const s=cnf(r.tr,r.p,h),stem=path.join(dir,"min-"+r.tr+"-"+r.p+"-"+h+"-"+budget);
  fs.writeFileSync(stem+".cnf",s);
  const z=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(budget),stem+".cnf",stem+".lrat"],{encoding:"utf8",windowsHide:true,timeout:50000});
  const verdict=z.status===10?"SAT":z.status===20?"UNSAT":"UNKNOWN",out={...r,h,budget,verdict};
  if(verdict==="UNSAT")out.check=await checkProof(s,stem+".lrat");
  fs.writeFileSync(stem+".json",JSON.stringify(out,null,2)+"\n");console.log(JSON.stringify(out));
 }
})().catch(e=>{console.error(e);process.exitCode=1;});
