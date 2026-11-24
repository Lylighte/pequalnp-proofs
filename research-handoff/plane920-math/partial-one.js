"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const {lines,weight:pc}=require("./plane-orbits"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const S=Number(process.argv[2]||4095),hist=JSON.parse(fs.readFileSync(path.join(__dirname,"small-core","partial-rank-"+S+".json"))),budget=Number(process.argv[3]||30000),start=Number(process.argv[4]||0),full=8191;let stop=Number(process.argv[5]||1e6);
const pts=Array.from({length:13},(_,i)=>i),ids=s=>pts.filter(i=>s&(1<<i)),stamp=Date.now(),rows=[...new Set([...lines,...ids(S).flatMap(i=>ids(lines[i]).map(p=>lines[i]^(1<<p)))])],at=new Map(rows.map((s,i)=>[s,i]));
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
const dir=path.join(__dirname,"small-core","partial-one");fs.mkdirSync(dir,{recursive:true});
function encode(aa,slotA,slotB){
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
  const localA=[];
  for(const p of ids(line)){
   for(let h=0;h<6;h++){
    if(h===slotA){if((aa>>l&1)&&!rr.some(i=>i!==l&&(aa>>i&1)&&(lines[i]>>p&1)))localA.push(option(p,13+h));}
    else if(h===slotB){own[h].push([l,option(p,13+h)]);}
    else if(h>=3){
     const chosen=option(p,13+h,line^(1<<p));own[h].push([l,chosen]);
     if(h===3){
      const pencils=[];
      for(const q of ids(line^(1<<p))){const z=v();pencils.push(z);for(const j of rr)if(!(lines[j]>>q&1))c(-z,nt(vals[at.get(lines[j])][13+h]));}
      c(-chosen,...pencils);
     }
    }
   }
  }
  if(localA.length){const tag=v();aused.push(tag);c(-tag,...localA);}
  for(let x=0;x<6;x++)for(let y=0;y<x;y++){
   if(x===slotA||y===slotA){if(!(aa>>l&1))continue;}
   else if(!(miss(aa)>>l&1))continue;
   option(13+y,13+x);
  }
  c(...opt);
  // Every target or its earliest active high has a four-point witness and hence needs two active lows.
  const lows=Array.from({length:6},(_,j)=>j).filter(j=>j!==slotA&&j!==slotB);
  for(const exc of lows)c(...lows.filter(j=>j!==exc).map(j=>vals[at.get(line)][13+j]));
 }
 for(let h=0;h<6;h++){
  if(h===slotB&&h>=4)continue;
  const opts=own[h];
  for(let j=0;j<opts.length;j++)for(let i=0;i<j;i++)if(opts[i][0]!==opts[j][0]){
   if(h!==slotB||h===2)c(-opts[i][1],-opts[j][1]);
   else for(let k=0;k<i;k++)if(opts[k][0]!==opts[i][0]&&opts[k][0]!==opts[j][0])c(-opts[k][1],-opts[i][1],-opts[j][1]);
  }
 }
 // At least three distinct targets were assigned a raw partner from high A.
 if(aused.length<3)c();else for(let y=0;y<aused.length;y++)for(let x=0;x<y;x++)c(...aused.filter((_,i)=>i!==x&&i!==y));
 return "p cnf "+nv+" "+cls.length+"\n"+cls.map(c=>c.join(" ")+" 0").join("\n")+"\n";
}
(async()=>{
 const totals={};
 const uniq=new Map(hist.recs.map(r=>[[r.a,r.hA,r.hB].join("-"),r]));
 const list=[...uniq.values()];stop=Math.min(stop,list.length);
 for(let i=start;i<stop;i++){
  const {a,hA,hB}=list[i],file=path.join(dir,S+"-"+a+"-"+hA+"-"+hB),s=encode(a,hA,hB);
  fs.writeFileSync(file+".cnf",s);
  const p=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(budget),file+".cnf",file+".lrat"],{encoding:"utf8",windowsHide:true,timeout:5000});
  const verdict=p.status===20?"UNSAT":p.status===10?"SAT":"UNKNOWN",res={i,a,hA,hB,S,budget,verdict};if(verdict==="UNSAT")res.check=await checkProof(s,file+".lrat");
  fs.writeFileSync(file+".json",JSON.stringify(res,null,2)+"\n");totals[verdict]=(totals[verdict]||0)+1;
  if(i%10===0)console.log(i,totals,Date.now()-stamp);
 }
 console.log({start,stop,totals,ms:Date.now()-stamp});
})().catch(e=>{console.error(e);process.exitCode=1;});
