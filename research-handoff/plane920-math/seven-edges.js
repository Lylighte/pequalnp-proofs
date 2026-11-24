"use strict";
const fs=require("node:fs"),path=require("node:path"),h=7,n=13,target=Number(process.argv[2]||9);
const weight=new Uint8Array(1<<21);for(let i=1;i<weight.length;i++)weight[i]=1+weight[i&(i-1)];
const ss=Array.from({length:128},(_,i)=>i),edge=ss.filter(s=>weight[s]===2),tri=ss.filter(s=>weight[s]===3),quad=ss.filter(s=>weight[s]===4);
const inside=ss.map(s=>edge.reduce((r,t,i)=>r|((t&s)===t?1<<i:0),0)),feats=[...ss.filter(s=>weight[s]===1),...edge,...tri,...quad],cap=feats.map(s=>[0,9,5,2,1][weight[s]]);
const absent=ss.map(s=>feats.map((f,i)=>(f&s)?-1:i).filter(i=>i>=0));
const gm=[];
function perm(list){if(list.length===7){gm.push(edge.map(e=>{let f=0;for(let j=0;j<7;j++)if(e>>j&1)f|=1<<list[j];return edge.indexOf(f);}));return;}
 for(let j=0;j<7;j++)if(!list.includes(j))perm([...list,j]);}
perm([]);
const seen=new Uint8Array(1<<21),recs=[],stamp=Date.now();
for(let g=0;g<seen.length;g++){
 if(seen[g]||weight[g]!==target)continue;
 const eidx=edge.flatMap((_,i)=>g>>i&1?[i]:[]);
 let os=0;for(const mp of gm){let t=0;for(const j of eidx)t|=1<<mp[j];if(!seen[t]){seen[t]=1;os++;}}
 const choices=[0,...eidx.map(i=>1<<i)].map(mark=>{
  const c=ss.filter(s=>weight[s]>=2&&(inside[s]&g)===mark);
  return c.filter(s=>!c.some(t=>s!==t&&(s&t)===s)).sort((a,b)=>weight[b]-weight[a]);
 });
 const rows=[...choices.slice(1),...Array.from({length:n-target},()=>choices[0])].sort((a,b)=>a.length-b.length);
 const rest=[...cap];let nodes=0,unknown=false;
 function dfs(i){if(i===n)return true;if(++nodes>180000){unknown=true;return false;}
  for(const s of rows[i]){const a=absent[s];if(a.some(j=>!rest[j]))continue;for(const j of a)rest[j]--;if(dfs(i+1))return true;for(const j of a)rest[j]++;if(unknown)return false;}
  return false;
 }
 const yes=dfs(0);recs.push({g,orbit:os,nodes,status:yes?"SAT":unknown?"UNKNOWN":"UNSAT"});
}
const sums={};for(const r of recs)sums[r.status]=(sums[r.status]||0)+r.orbit;
const result={target,sums,recs,ms:Date.now()-stamp};fs.writeFileSync(path.join(__dirname,"small-core","seven-edges-"+target+".json"),JSON.stringify(result,null,2)+"\n");console.log(target,sums,recs.length,result.ms);
