"use strict";
const fs=require("node:fs"),cp=require("node:child_process"),path=require("node:path"),{lines,weight:w}=require("./plane-orbits"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const filedir=path.join(__dirname,"small-core","five-partial"),summ=path.join(__dirname,"small-core","five-target-signatures.json");fs.mkdirSync(filedir,{recursive:true});
const families=JSON.parse(fs.readFileSync(summ)),pts=Array.from({length:13},(_,i)=>i),ids=m=>pts.filter(i=>m>>i&1),bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
const K=Number(process.argv[2]||1),budget=Number(process.argv[3]||30000),lo=Number(process.argv[4]||0),hi=Number(process.argv[5]||1e6),more=process.argv.includes("--rich");
function encode(S,pre,rows){
 const order=ids(S),tt=order.map(i=>lines[i]),at=new Map(rows.map((r,i)=>[r,i])),cols=ids(tt.reduce((a,b)=>a|b)),n=cols.length,top=[],cc=[];
 let ctr=0;const v=()=>++ctr,ng=x=>typeof x==="boolean"?!x:-x,c=(...s)=>{if(!s.includes(true))cc.push(s.filter(x=>x!==false));};
 const vals=rows.map(r=>cols.map(p=>!!(r>>p&1))),isHigh=v(),own=[],final=[];
 for(let g=0;g<5;g++){
  const arms=[],sels=[];for(let side=0;side<2;side++){
   const sel=Array.from({length:n+g},v);sels.push(sel);
   arms.push(vals.map(sig=>{const hits=sel.flatMap((s,j)=>{const a=sig[j];if(a===false)return [];if(a===true)return [s];const z=v();c(-z,a);c(-z,s);c(z,-a,-s);return [z];});const z=v();for(const a of hits)c(-a,z);c(-z,...hits);return z;}));
  }
  top.push(sels);let equal=true;for(let j=n+g-1;j>=0;j--){const a=sels[0][j],b=sels[1][j],nx=v();c(ng(equal),-a,b);c(ng(equal),a,b,nx);c(ng(equal),-a,-b,nx);equal=nx;}
  for(let i=0;i<rows.length;i++){const row=rows[i],j=tt.indexOf(row),a=arms[0][i],b=arms[1][i],z=(g<pre.length&&j>=0)?!!(pre[g]>>j&1):v();
   c(ng(z),a);c(ng(z),b);c(z,-a,-b);vals[i].push(z);if(g===4&&w[row]<=3)c(-isHigh,ng(z));}
 }
 for(let h=1;h<32;h++)if(w[h]<=3){
  const required=[0,2,4,5][w[h]];
  for(let mask=0;mask<32;mask++)if(w[mask]===6-required)c(...ids(mask).flatMap(g=>ids(h).map(i=>vals[at.get(tt[i])][n+g])));
 }
 for(const [j,line] of tt.entries()){
  const opts=[];function option(x,y,e,high){const t=v();opts.push({t,x,y});
   for(let i=0;i<rows.length;i++){const r=rows[i],a=vals[i][x],b=vals[i][y];
    if(r===line){c(-t,a);c(-t,b);}else c(-t,ng(a),ng(b));
    if(e!==undefined&&w[r]<=3)c(-t,...(high?[isHigh]:[]),r===e?b:ng(b));
   }
   return t;
  }
  for(const p of ids(line))for(const g of [3,4]){
   const t=option(cols.indexOf(p),n+g,line^(1<<p),g===4);
   // Low g4 and high g5 raw users have their true lines in a pencil through a point of L other than p.
   const labs=ids(line^(1<<p)).map(q=>{const z=v();for(let i=0;i<5;i++)if(!(tt[i]>>q&1))c(-z,ng(vals[at.get(tt[i])][n+g]));return z;});
   c(-t,...(g===4?[-isHigh]:[]),...labs);own.push({j,g,t});
  }
  for(let a=0;a<5;a++)for(let b=0;b<a;b++)if(a!==1)option(n+b,n+a);
  c(...opts.map(o=>o.t));final.push(opts);
 }
 for(let a=0;a<own.length;a++)for(let b=0;b<a;b++)if(own[a].g===own[b].g&&own[a].j!==own[b].j)c(-own[a].t,-own[b].t,...(own[a].g===4?[isHigh]:[]));
 if(process.argv.includes("--damage")){
  for(let d=1;d<32;d++)if(w[d]<=2){
   const survived=[];
   for(const [j,row] of tt.entries()){
    const sig=cols.map(p=>!!(row>>p&1));
    for(let g=0;g<5;g++){
     if(d>>g&1){sig.push(false);continue;}
     const side=top[g].map(m=>{const hits=m.flatMap((s,k)=>{const a=sig[k];if(a===false)return [];if(a===true)return [s];const f=v();c(-f,a);c(-f,s);c(f,-a,-s);return [f];});const z=v();for(const x of hits)c(-x,z);c(-z,...hits);return z;});
     const z=v();c(-z,side[0]);c(-z,side[1]);c(z,-side[0],-side[1]);sig.push(z);
    }
    const z=v();survived.push(z);for(const a of final[j])c(-a.t,ng(sig[a.x]),ng(sig[a.y]),z);
   }
   for(let mask=0;mask<32;mask++)if(w[mask]===4-w[d])c(...ids(mask).map(i=>-survived[i]));
  }
 }
 return {cnf:"p cnf "+ctr+" "+cc.length+"\n"+cc.map(z=>z.join(" ")+" 0").join("\n")+"\n",top,final,tt,cols};
}
module.exports={encode};
if(require.main===module)(async()=>{
 const jobs=[];for(const f of families){const uniq=new Map(f.rows.map(r=>[r.slice(0,K).join("-"),r.slice(0,K)]));for(const pre of uniq.values())jobs.push({S:f.S,pre});}
 const known=new Set();if(process.argv.includes("--skip"))for(const fn of fs.readdirSync(filedir).filter(x=>x.endsWith(".json"))){const r=JSON.parse(fs.readFileSync(path.join(filedir,fn),"utf8"));if(r.verdict==="UNSAT")known.add([r.S,...r.pre].join("-"));}
 const start=Date.now(),summary={};for(let i=lo;i<Math.min(hi,jobs.length);i++){
  const {S,pre}=jobs[i];if(pre.some((_,i)=>known.has([S,...pre.slice(0,i+1)].join("-")))){summary.skipped=(summary.skipped||0)+1;continue;}const tt=ids(S).map(j=>lines[j]),u=tt.reduce((a,b)=>a|b),every=Array.from({length:8192},(_,i)=>i).filter(i=>!(i&~u)&&w[i]<=4);
  const rows=[...new Set([...tt,...tt.flatMap(l=>ids(l).map(p=>l^(1<<p))),...(more?every.filter(r=>w[r]===4&&tt.some(l=>w[r&l]>=3)):[])])],stem=path.join(filedir,S+"-"+pre.join("-")+"-"+budget+(more?"-rich":"")+(process.argv.includes("--damage")?"-damage":""));
  let out={S,pre,budget,i};for(let turn=0;turn<=8;turn++){
   const {cnf,top,final,cols}=encode(S,pre,rows);fs.writeFileSync(stem+".cnf",cnf);
   const run=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(budget),stem+".cnf",stem+".lrat"],{encoding:"utf8",windowsHide:true,timeout:4200});
   if(run.status===20){out.verdict="UNSAT";out.check=cnf.includes("\n 0\n")?{inputEmpty:true,empty:true}:await checkProof(cnf,stem+".lrat");break;}
   if(run.status!==10){out.verdict="UNKNOWN";break;}
   const yes=new Set(run.stdout.split(/\r?\n/).filter(l=>l.startsWith("v ")).flatMap(l=>l.slice(2).split(/\s+/).map(Number)).filter(x=>x>0)),sels=top.map(g=>g.map(menu=>menu.flatMap((s,j)=>yes.has(s)?[j]:[]))),end=final.map(opt=>opt.find(x=>yes.has(x.t)));
   const miss=every.filter(row=>{const vals=cols.map(p=>!!(row>>p&1));for(const g of sels)vals.push(g.every(menu=>menu.some(j=>vals[j])));return end.some(({x,y},j)=>(vals[x]&&vals[y])!==(tt[j]===row));});
   if(!miss.length){out.verdict="SAT";out.model={cols,sels,end};break;}
   if(turn===8){out.verdict="RELAXED";break;}rows.push(...miss.filter((_,j)=>j%Math.ceil(miss.length/16)===0));
  }
  out.rows=rows;fs.writeFileSync(stem+".json",JSON.stringify(out)+"\n");summary[out.verdict]=(summary[out.verdict]||0)+1;
  if(i%50===0)console.log(i,jobs.length,summary,Date.now()-start);
 }
 console.log({summary,ms:Date.now()-start});
})().catch(e=>{console.error(e);process.exitCode=1;});
