const fs=require('node:fs'),path=require('node:path');
const {table,mult,join,raw,pm,pc}=require('./three-or-five-lines.cjs'),{choices}=require('./refine-four-nine.cjs'),{pricedTables}=require('./paid-or-arms.cjs');
const six=process.argv.includes('--six'),k=six?6:7,budget=six?7:8;
const records=require(six?'./six-target-last-or-100000-pay3.json':'./seven-target-last-or-100000-pay3.json'),results=[];
for(const fam of records.out)for(const r of fam.sample){
 const gs=[...r.terms];
 const arm=([p,j])=>gs.reduce((v,f,k)=>j&1<<k?mult(v,f):v,p<0?[0]:[1<<p]);
 for(const i of [0,2])gs.push(join(arm(r.pairs[i]),arm(r.pairs[i+1])));
 const flags=gs.map(table),options=flags.map((v,i)=>choices(gs.slice(0,i),v));
 let checked=0,live=null;
 function walk(i,known,fixed,cuts){
  if(i===5){
   checked++;const q=pricedTables(flags,[...fixed],k,budget,fam.m,2,cuts,true);
   if(q.found)live={paid:[...fixed].map(v=>v.toString(16)),cuts,q};
   return;
  }
  for(const [a,b] of options[i]){
   const x=pm(a),y=pm(b),d=x&~y&fam.m,e=y&~x&fam.m;if(pc[d]<2||pc[e]<2)continue;
   if(!six&&(pc[d]===2&&cuts.some(s=>(s&fam.m)===d)||pc[e]===2&&cuts.some(s=>(s&fam.m)===e)))continue;
   const f=new Set(fixed);if(!known.has(a))f.add(a);if(!known.has(b))f.add(b);
   if([...f].some(t=>pc[pm(t)&fam.m]<3))continue;
   walk(i+1,new Set([...known,flags[i]]),f,[...cuts,x&~y,y&~x]);if(live)return;
  }
 }
 walk(0,new Set(raw),new Set(),[]);results.push({m:fam.m,checked,live});
}
const out={records:results.length,physical:results.reduce((n,r)=>n+r.checked,0),witnesses:results.filter(r=>r.live)};
fs.writeFileSync(path.join(__dirname,six?'refine-six-five-pay3.json':'refine-seven-five.json'),JSON.stringify(out)+'\n');console.log({records:out.records,physical:out.physical,witnesses:out.witnesses.length});
