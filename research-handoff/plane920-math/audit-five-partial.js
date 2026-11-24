"use strict";
const fs=require("node:fs"),path=require("node:path"),assert=require("node:assert/strict"),{check}=require("../plane920-search/check-rup.cjs");
const {perm,lines,apply,weight:w}=require("./plane-orbits"),{encode}=require("./five-partial");
const d=path.join(__dirname,"small-core","five-partial"),checker=path.join(__dirname,"..","plane920-search");
const inp=fs.readdirSync(d).filter(f=>f.endsWith(".json")).map(f=>({...JSON.parse(fs.readFileSync(path.join(d,f))),name:f.slice(0,-5)})).filter(x=>x.verdict==="UNSAT");
const maps=perm.map(g=>lines.map(l=>lines.indexOf(apply(l,g)))),pencils=Array.from({length:13},(_,i)=>lines.reduce((m,l,j)=>m|((l>>i&1)<<j),0));
const fullClasses=new Set(),picked=new Map(),points=[0,1,2,3,4],population=[];
for(const S of [31,87,143]){
 const tt=lines.flatMap((l,i)=>S>>i&1?[i]:[]),loc=r=>tt.reduce((m,id,i)=>m|((r>>id&1)<<i),0),aut=[];
 const orb=new Set();for(const mp of maps){const s=apply(S,mp);orb.add(s);if(s===S)aut.push(tt.map(i=>tt.indexOf(mp[i])));}
 for(const a of orb){assert(!fullClasses.has(a));fullClasses.add(a);}
 const pencil=pencils.map(loc),dense=Array.from({length:32},(_,i)=>i).filter(r=>w[r]>=3),pencilOK=dense.map(r=>pencil.some(q=>(q&r)===r));
 const locMaps=aut.map(g=>Array.from({length:32},(_,r)=>apply(r,g)));
 const proofFor=new Map();
 for(const z of inp.filter(z=>z.S===S).sort((a,b)=>a.pre.length-b.pre.length||(a.check.add||0)-(b.check.add||0))){
  for(const m of locMaps){let acc=1;for(const t of z.pre)acc=acc*32+m[t];if(!proofFor.has(acc))proofFor.set(acc,z);}
 }
 let matched=0,admissible=0;
 for(let code=0;code<16**5;code++){
  const R=points.map(i=>dense[(code>>>(4*i))&15]);
  if(points.some(i=>points.some(j=>j<i&&w[(31^R[i])&(31^R[j])]>1)))continue;
  const need=points.filter(l=>!points.some(i=>points.some(j=>j<i&&i>1&&(R[i]&R[j])===(1<<l))));
  // Assign required raw rows to helper 4 (low, at most one) or helper 5.
  const can=g=>need.filter(l=>pencil.some(q=>(q&R[g])===(1<<l)));
  const fourth=pencil.some(q=>(R[3]&q)===R[3])?can(3):[],fifth=can(4),limit=pencil.some(q=>(R[4]&q)===R[4])?5:1;
  if(![-1,...fourth].some(j=>need.filter(i=>i!==j).every(i=>fifth.includes(i))&&need.length-Number(j!==-1)<=limit))continue;
  admissible++;let acc=1,certificate;for(const r of R){acc=acc*32+r;if(proofFor.has(acc)){certificate=proofFor.get(acc);break;}}
  if(certificate){matched++;picked.set(certificate.name,certificate);}
  else throw Error("Uncovered "+S+" "+R.join(","));
 }
 population.push({S,planeOrbit:orb.size,tuples:16**5,admissible,matched});
}
assert.equal(fullClasses.size,1287);
const checks=[];
for(const [name,z] of picked){
 const stem=path.join(d,name),stored=fs.readFileSync(stem+".cnf","utf8"),regenerated=encode(z.S,z.pre,z.rows).cnf;
 assert.equal(regenerated,stored);let adds=0;
 if(!stored.includes("\n 0\n")){const a=check(path.relative(checker,stem+".cnf"),path.relative(checker,stem+".lrat"));assert(a.empty);adds=a.adds;}
 checks.push({name,adds});
}
const result={population,receipts:checks.length,totalRupAdds:checks.reduce((a,b)=>a+b.adds,0),checks};
fs.writeFileSync(path.join(__dirname,"small-core","five-partial-audit.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify({...result,checks:undefined}));
