"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const {lines,weight:pc,perm,apply}=require("./plane-orbits"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const S=Number(process.argv[2]||4095),budget=Number(process.argv[3]||30000),start=Number(process.argv[4]||0),full=8191;let stop=Number(process.argv[5]||1e6);
const pts=Array.from({length:13},(_,i)=>i),ids=s=>pts.filter(i=>s&(1<<i)),stamp=Date.now(),rows=[...new Set([...lines,...ids(S).flatMap(i=>ids(lines[i]).map(p=>lines[i]^(1<<p)))])],at=new Map(rows.map((s,i)=>[s,i]));
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
const dir=path.join(__dirname,"small-core","partial-ten");fs.mkdirSync(dir,{recursive:true});
function encode(aa,forceL,more){const slotA=5,slotB=-1;
 const n=pc[S],rr=ids(S),cls=[];let nv=0;const v=()=>++nv,nt=a=>typeof a==="boolean"?!a:-a;
 const vals=rows.map(r=>pts.map(p=>!!(r&(1<<p))));
 function c(...xs){if(!xs.includes(true))cls.push(xs.filter(x=>x!==false));}
 for(let h=0;h<6;h++){
  const arms=[],menus=[];
  for(let side=0;side<2;side++){
   const menu=Array.from({length:13+h},v);menus.push(menu);
   arms.push(vals.map(sig=>{
    const hits=menu.flatMap((a,j)=>{const b=sig[j];if(b===false)return [];if(b===true)return [a];const z=v();c(-z,a);c(-z,b);c(z,-a,-b);return [z];});
    const z=v();for(const a of hits)c(-a,z);c(-z,...hits);return z;
   }));
  }
  let prev=true;for(let j=13+h-1;j>=0;j--){const a=menus[0][j],b=menus[1][j],eq=v();c(nt(prev),-a,b);c(nt(prev),-a,-b,eq);c(nt(prev),a,b,eq);prev=eq;}
  for(let r=0;r<rows.length;r++){const a=arms[0][r],b=arms[1][r],i=lines.indexOf(rows[r]);
   const z=(h===slotA||h===slotB)&&pc[rows[r]]<=3?false:h===slotA&&i>=0&&(S>>i&1)?!!(aa&(1<<i)):v();
   c(nt(z),a);c(nt(z),b);c(z,-a,-b);vals[r].push(z);}
 }
 for(let t=1;t<=full;t++)if(!(t&~S)&&pc[t]<=3){
  const need=[0,2,4,5][pc[t]];
  for(let h=1;h<64;h++)if(pc[h]===7-need)c(...ids(h).flatMap(j=>ids(t).map(l=>vals[at.get(lines[l])][13+j])));
 }
 const own=Array.from({length:6},()=>[]),aused=[];
 function miss(m){const z=S^m;if(pc[z]>=6)return 0;if(pc[z]===5)return z;return S;}
 for(const l of rr){
  const opt=[],line=lines[l];
  function option(lo,hi,extra){
   const t=v();opt.push(t);
   for(let r=0;r<rows.length;r++){const a=vals[r][lo],b=vals[r][hi];
    if(rows[r]===line){c(-t,a);c(-t,b);}else c(-t,nt(a),nt(b));
    if(extra!==undefined&&pc[rows[r]]<=3)c(-t,rows[r]===extra?b:nt(b));
   }
   return t;
  }
  if(aa>>l&1){
   for(const p of ids(line))if(!rr.some(i=>i!==l&&(aa>>i&1)&&(lines[i]>>p&1)))option(p,18);
  }else if(l===forceL){
   for(const p of ids(line))option(p,17,line^(1<<p));
  }else{
   for(let x=0;x<5;x++)for(let y=0;y<x;y++)option(13+y,13+x);
  }
  c(...opt);
  for(let exc=0;exc<5;exc++)c(...[0,1,2,3,4].filter(j=>j!==exc).map(j=>vals[at.get(line)][13+j]));
 }
 return "p cnf "+nv+" "+cls.length+"\n"+cls.map(c=>c.join(" ")+" 0").join("\n")+"\n";
}
(async()=>{
 const totals={};
 const group=perm.map(p=>lines.map(l=>lines.indexOf(apply(l,p)))).filter(g=>apply(S,g)===S);
 const doneA=new Set(),list=[];
 for(let a=0;a<=8191;a++){
  if(pc[a]!==6||(a&~S)||doneA.has(a))continue;
  const aut=[];for(const g of group){const b=apply(a,g);doneA.add(b);if(a===b)aut.push(g);}
  if(ids(a).some(l=>!ids(lines[l]).some(p=>!ids(a).some(j=>j!==l&&(lines[j]>>p&1)))))continue;
  const seen=new Set();
  for(const l of ids(S&~a))if(!seen.has(l)){
   for(const g of aut)seen.add(g[l]);list.push({a,l});
  }
 }
 stop=Math.min(stop,list.length);console.log({representatives:list.length});
 for(let i=start;i<stop;i++){
  const {a,l}=list[i],file=path.join(dir,S+"-"+a+"-"+l),s=encode(a,l);
  fs.writeFileSync(file+".cnf",s);
  const p=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(budget),file+".cnf",file+".lrat"],{encoding:"utf8",windowsHide:true,timeout:10000});
  const verdict=p.status===20?"UNSAT":p.status===10?"SAT":"UNKNOWN",res={i,a,l,S,budget,verdict};if(verdict==="UNSAT")res.check=await checkProof(s,file+".lrat");
  fs.writeFileSync(file+".json",JSON.stringify(res,null,2)+"\n");totals[verdict]=(totals[verdict]||0)+1;
  if(i%10===0)console.log(i,totals,Date.now()-stamp);
 }
 console.log({start,stop,totals,ms:Date.now()-stamp});
})().catch(e=>{console.error(e);process.exitCode=1;});
