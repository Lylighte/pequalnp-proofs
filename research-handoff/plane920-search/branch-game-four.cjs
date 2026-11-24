const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {lines}=require('./branch-game.json'),full=8191,pc=new Uint8Array(8192);
for(let i=1;i<=full;i++)pc[i]=1+pc[i&(i-1)];
const star=Array.from({length:13},(_,p)=>lines.reduce((m,L,i)=>m+(L&(1<<p)?1<<i:0),0));
const id=new Map([0,full,...Array.from({length:13},(_,i)=>1<<i),...star].map((x,i)=>[x,i]));
const exact=process.argv.includes('--exact');
const onLines=Array.from({length:8192},(_,m)=>lines.reduce((s,L,i)=>s+Number((L&m)===m)*(1<<i),0));
const mins=values=>[...new Set(values)].filter((m,_,v)=>!v.some(t=>t!==m&&(t&m)===t)).sort((a,b)=>a-b);
const sig=Array.from(id.keys()),at=sig.map(x=>pc[x]);
const unrestricted=[pc];
for(let t=1;t<4;t++){
 const prev=unrestricted.at(-1),cur=new Uint8Array(8192);
 for(let s=0;s<=full;s++){
   let z=prev[s];for(const a of sig)for(const b of sig)z=Math.min(z,Math.max(prev[s&~(a&~b)],prev[s&~(b&~a)]));
   cur[s]=z;
 }
 unrestricted.push(cur);
}
const affine=[];
for(const z of [1,3,9])for(let k=0;k<13;k++)affine.push(Array.from({length:13},(_,i)=>(z*i+k)%13));
const setL=new Set(lines);for(const p of affine)for(const L of lines){
 let m=0;for(let v=0;v<13;v++)if(L&(1<<v))m|=1<<p[v];assert(setL.has(m));
}
const roots=[],seen=new Set();
for(let x=0;x<13;x++)for(let y=x+1;y<13;y++){
 if(seen.has([x,y].join()))continue;
 const orbit=new Set(affine.map(p=>[p[x],p[y]].sort((a,b)=>a-b).join()));orbit.forEach(v=>seen.add(v));roots.push({x,y,weight:orbit.size});
}
assert.equal(seen.size,78);
const threshold=5,profile={},examples={},counts={prefix:[0,0,0,0,0],critical:0,rawcritical:0,mixedcritical:0},byroot=[];
const excess=[null,Uint8Array.from(pc,k=>2*k)];
for(let h=2;h<=4;h++){
 const prev=excess[h-1],cur=new Uint8Array(8192);
 for(let s=0;s<=full;s++){
   let best=255;
   for(const a of sig)for(const b of sig){
     let z=1+Math.max(prev[s&~(a&~b)],prev[s&~(b&~a)]);
     if(pc[a]===1||pc[b]===1)z=Math.max(z,prev[s]);
     best=Math.min(best,z);
   }
   cur[s]=Math.max(best,2*Math.min(4,pc[s]));
 }
 excess.push(cur);
}
const repro={},orderData={},restr={},records=[];
const keyFor=a=>a.join(',');
function arms(paths,j){
 const list=[],seen=new Set();
 for(let p=-1;p<13;p++)for(let J=0;J<1<<j;J++){
   if(p===-1&&!J)continue;
   const masks=paths.map(q=>{let v=p===-1?0:1<<p;for(let k=0;k<j;k++)if(J&(1<<k))v|=q.raw[k];return v;});
   const a=masks.map(v=>onLines[v]),terms=mins(masks);
   if(exact&&pc[terms.reduce((z,m)=>z&m,full)]>=2)continue;
   const key=keyFor(exact?masks:a);if(seen.has(key))continue;
   seen.add(key);list.push({v:a,masks,terms,termKey:terms.join(','),p,J});
 }
 return list;
}
function run(j,paths,tree,firstNonbare,bestRepair,root,used){
 counts.prefix[j]++;
 const level=unrestricted[3-j],options=arms(paths,j),n=paths.length;
 const criticalRows=paths.map((p,i)=>i).sort((a,b)=>pc[paths[b].s]-pc[paths[a].s]);
 for(let i=0;i<options.length;i++)for(let l=0;l<(exact?i:i+1);l++){
   const u=options[i],v=options[l],next=[];
   let low=0,high=0,non=firstNonbare,repair=bestRepair;
   for(const k of criticalRows){
     const s=paths[k].s,a=u.v[k],b=v.v[k],s1=s&~(b&~a),s2=s&~(a&~b);
     if(level[s1]>=threshold||level[s2]>=threshold){high=1;break;}
     if(!non&&(at[id.get(a)]!==4||at[id.get(b)]!==4))non=j+1;
     if(at[id.get(a)]===1||at[id.get(b)]===1)repair=Math.max(repair,13+j+excess[4-j][s]);
     low=Math.max(low,pc[s1],pc[s2]);
     if(j<3){next[2*k]={s:s1,raw:[...paths[k].raw,u.masks[k]]};next[2*k+1]={s:s2,raw:[...paths[k].raw,v.masks[k]]};}
   }
   if(high)continue;
   const combined=exact?mins([...u.terms,...v.terms]).join(','):'';
   if(exact&&(combined===u.termKey||combined===v.termKey||used.includes(combined)))continue;
   const t=[...tree,[[u.p,u.J],[v.p,v.J]]];
   if(j<3)run(j+1,next,t,non,repair,root,[...used,combined]);
   else{
     counts.critical++;if(non)counts.mixedcritical++;else counts.rawcritical++;
     const label=[root,low,non?'mixed':'allStars'].join(':');profile[label]=(profile[label]||0)+1;
     if(exact)records.push(...t.flat().map(([p,J])=>(p+1)*8+J));
     if(!examples[label])examples[label]=t;
     const proved=Math.max(repair,17+2*low),rk=[root,low,non||0,proved].join(':');
     repro[rk]=(repro[rk]||0)+1;
     if(proved<27){
       const pts=new Set(t.flat().map(q=>q[0]).filter(p=>p>=0));
       const key=[low,non||0,pts.size].join(':');orderData[key]=(orderData[key]||0)+1;
       if(!restr[rk])restr[rk]=t;
     }
   }
 }
}
for(const {x,y,weight} of roots){
 const before=counts.critical,a=star[x],b=star[y];
 run(1,[{s:full&~(b&~a),raw:[1<<x]},{s:full&~(a&~b),raw:[1<<y]}],[[[x,0],[y,0]]],0,0,[x,y].join(','),[[1<<x,1<<y].sort((a,b)=>a-b).join(',')]);
 byroot.push({x,y,weight,critical:counts.critical-before});
}
const ret={threshold,exact,normalForm:'The fixed raw part of an OR input is empty or one point (mandatory-pair reduction); any subset of earlier resolved ORs may also be multiplied. Signature mode allows equal signature vectors, exact mode uses raw-resolution vectors and removes globally redundant ORs.',counts,byroot,profile,examples,repairBounds:repro,survivorsByRepresentativeSupport:orderData,remainingExamples:restr};
if(exact){
 const data=Buffer.from(records),gzip=require('node:zlib').gzipSync(data,{level:9});
 ret.certificate={uncompressedBytes:data.length,compressedBytes:gzip.length,sha256:require('node:crypto').createHash('sha256').update(data).digest('hex')};
 fs.writeFileSync(path.join(__dirname,'branch-game-four-records.gz'),gzip);
}
fs.writeFileSync(path.join(__dirname,exact?'branch-game-four-exact.json':'branch-game-four.json'),JSON.stringify(ret,null,2)+'\n');console.log({counts,byroot,profile});
