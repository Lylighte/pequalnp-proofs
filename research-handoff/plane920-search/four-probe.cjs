const fs=require('node:fs'),path=require('node:path');
const {test,allLines}=require('./local-exact.cjs');
let ids;
for(let k=3;k<13&&!ids;k++){
 const x=[0,1,2,k],seen=new Map();
 for(const i of x)for(const v of allLines[i])seen.set(v,1+(seen.get(v)||0));
 if(Math.max(...seen.values())===2)ids=x;
}
const active=[...new Set(ids.flatMap(i=>allLines[i]))].sort((a,b)=>a-b);
const inc=active.map(v=>ids.reduce((m,L,i)=>m+Number(allLines[L].includes(v))*(1<<i),0));
const perm=[];
function gen(prefix,rest){if(!rest.length){perm.push(prefix);return;}for(const r of rest)gen([...prefix,r],rest.filter(x=>x!==r));}
gen([],[0,1,2,3]);
const maps=perm.map(p=>inc.map(m=>inc.indexOf(p.reduce((s,t,i)=>s+((m>>i)&1)*(1<<t),0))));
const seen=new Set,reps=[];
for(let x=0;x<active.length;x++)for(let y=x+1;y<active.length;y++){
 const s=x+','+y;if(seen.has(s))continue;
 const orbit=new Set(maps.map(t=>[t[x],t[y]].sort((a,b)=>a-b).join(',')));orbit.forEach(z=>seen.add(z));
 reps.push([x,y,orbit.size]);
}
const records=[],rows=[];
const base={requireTwoOr:true,sensitivity:true,live:false,order:true,swaps:false,rows,conflicts:20000,ms:3500};
for(const [x,y,orbit] of reps)for(const op of [false,true]){
 const r=test(ids,11,base,[x,y,op]);records.push({first:[x,y,op],orbit,...r,bad:r.bad?.length});
 if(r.bad)rows.push(...r.bad.filter(w=>!rows.includes(w)).slice(0,8));
 console.log(ids,[x,y,op],r.status,r.ms,r.rows,r.bad?.length);
}
fs.writeFileSync(path.join(__dirname,'four-quadrilateral-probe.json'),JSON.stringify({ids,active,inc,reps,records,rows},null,2)+'\n');
