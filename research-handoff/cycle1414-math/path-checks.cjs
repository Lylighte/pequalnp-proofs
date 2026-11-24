'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');

const paths=n=>Array.from({length:n-1},(_,i)=>[i,i+1]);
const active=(m,j)=>!!(m&(1<<j));
const graph=(n,edges)=>Array.from({length:2**n},(_,m)=>edges.some(([u,v])=>active(m,u)&&active(m,v)));
function robustPairs(n,f){
 const remains=(i,j,b)=>f.some((v,m)=>!active(m,i)&&active(m,j)===b&&v!==f[m|(1<<i)]);
 const res=[];
 for(let i=0;i<n;i++)for(let j=0;j<i;j++){
  const robust=[i,j].map((t,k)=>[false,true].every(b=>remains(t,k?i:j,b)));
  assert(robust.some(Boolean));res.push({i,j,robust});
 }return res;
}
const p4=robustPairs(4,graph(4,paths(4))),p6=robustPairs(6,graph(6,paths(6)));
const cuts=Array.from({length:6},(_,r)=>{
 const edges=paths(6).filter(e=>!e.includes(r)),vertices=[...new Set(edges.flat())];
 const complete=[];
 for(let a=0;a<64;a++)if(vertices.some(v=>active(a,v))&&vertices.some(v=>!active(a,v))){
   const e=new Set(edges.map(x=>x.join(',')));if(vertices.every(u=>vertices.every(v=>u>=v||(e.has([u,v].join(','))===(active(a,u)!==active(a,v))))))complete.push(a);
 }
 assert.equal(complete.length,0);
 return {r,edges,completeBipartitions:complete.length};
});
const starFormula=[];for(let m=0;m<128;m++){
 const e=paths(7).concat([[6,0]]);
 const f=e.some(([a,b])=>active(m,a)&&active(m,b));
 const restricted=m&126;
 const edgeR=paths(6).some(([a,b])=>active(restricted,a+1)&&active(restricted,b+1));
 if(!(m&1))assert.equal(f,edgeR);
 if(m&1)assert.equal(f,active(m,1)||active(m,6)||[[2,3],[3,4],[4,5]].some(([a,b])=>active(m,a)&&active(m,b)));
}fs.writeFileSync('path-checks.json',JSON.stringify({p4,p6,cuts},null,2)+'\n');
console.log(JSON.stringify({strongUnorderedP4:p4.length,strongUnorderedP6:p6.length,vertexDeletedP6NeverCompleteBipartite:cuts.length,cycleRestrictionRows:128}));
