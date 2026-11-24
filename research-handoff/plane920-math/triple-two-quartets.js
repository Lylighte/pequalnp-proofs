"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const {checkProof}=require("../plane920-search/stream-rup.cjs");
const dir=path.join(__dirname,"small-core","shared-high"),weight=n=>n.toString(2).replace(/0/g,"").length;
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
function encode(k,h,nr=1){
 const n=8,all=(1<<n)-1,t=7,neg=[],pos=[t,1+8+16+32,2+8+64+128];
 for(let r=0;r<=all;r++)if(r!==t&&weight(r)===3)neg.push(r);
 const rows=[...pos,...neg],sigs=rows.map(r=>Array.from({length:n},(_,i)=>!!(r&(1<<i)))),cl=[];
 let nv=0;const v=()=>++nv,nt=a=>typeof a==="boolean"?!a:-a;
 function c(...a){if(!a.includes(true))cl.push(a.filter(x=>x!==false));}
 for(let g=0;g<h;g++){
  const menu=[],arms=[];
  for(let i=0;i<2;i++){
   const s=Array.from({length:n+g},v);menu.push(s);
   arms.push(sigs.map(sig=>{
    const hits=s.flatMap((a,j)=>{const b=sig[j];if(b===false)return [];if(b===true)return [a];const z=v();c(-z,a);c(-z,b);c(z,-a,-b);return [z];});
    const z=v();for(const a of hits)c(-a,z);c(-z,...hits);return z;
   }));
  }
  let prev=true;for(let j=n+g-1;j>=0;j--){const a=menu[0][j],b=menu[1][j],eq=v();c(nt(prev),-a,b);c(nt(prev),-a,-b,eq);c(nt(prev),a,b,eq);prev=eq;}
  for(let r=0;r<rows.length;r++){const a=arms[0][r],b=arms[1][r],z=v();c(-z,a);c(-z,b);c(z,-a,-b);sigs[r].push(z);if(g===h-1)c(r<pos.length?z:-z);}
 }
 return "p cnf "+nv+" "+cl.length+"\n"+cl.map(a=>a.join(" ")+" 0").join("\n")+"\n";
}
(async()=>{
 for(const h of [4,5])for(const k of [0]){
  const s=encode(k,h),stem=path.join(dir,"triple-two-quartets-"+h);
  fs.writeFileSync(stem+".cnf",s);const proc=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c","100000",stem+".cnf",stem+".lrat"],{encoding:"utf8",windowsHide:true,timeout:20000});
  const verdict=proc.status===20?"UNSAT":proc.status===10?"SAT":"UNKNOWN",out={h,k,verdict};if(verdict==="UNSAT")out.check=await checkProof(s,stem+".lrat");
  console.log(out);fs.writeFileSync(stem+".json",JSON.stringify(out,null,2)+"\n");
 }
})().catch(e=>{console.error(e);process.exitCode=1;});
