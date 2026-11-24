'use strict';
const fs=require('node:fs'),path=require('node:path');
const full=8191;
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,x)=>m|1<<((x+i)%13),0));
const pc=new Uint8Array(full+1);
for(let i=1;i<=full;i++) pc[i]=pc[i&(i-1)]+1;
const lb=new Uint8Array(full+1),witness=new Uint16Array(full+1);
for(let U=1;U<=full;U++){
  const family=lines.filter(L=>(L&U)===L);
  if(!family.length)continue;
  let best=255, bestA=0;
  for(let A=(U-1)&U;A>0;A=(A-1)&U){
    const B=U^A;
    if(A>B || lb[A]+lb[B]>=best)continue;
    const cells=family.filter(L=>(L&A)&&(L&B)).map(L=>[L&A,L&B]);
    const first=[0,...new Set(cells.map(t=>t[0]))],second=[0,...new Set(cells.map(t=>t[1]))];
    const normal=2*cells.length;
    let save=0;
    for(const p of first)for(const q of second){
      let cur=0;
      for(const [x,y] of cells)cur+=Math.max(p===x?pc[y]-1:0,q===y?pc[x]-1:0);
      save=Math.max(save,cur);
    }
    const cost=lb[A]+lb[B]+normal-save;
    if(cost<best){best=cost;bestA=A;}
  }
  lb[U]=best;witness[U]=bestA;
}
const dist={};for(let s=1;s<=full;s++){const k=pc[s];(dist[k]??={})[lb[s]]=((dist[k]??{})[lb[s]]||0)+1;}
let U=full,chain=[];while(witness[U]){const a=witness[U],b=U^a;chain.push([U,a,b,lb[U]]);U=pc[a]>pc[b]?a:b;}
const summary={fullBound:lb[full],bySize:dist,oneMinimizingChain:chain};
fs.writeFileSync(path.join(__dirname,'merge-recursion.json'),JSON.stringify(summary,null,2)+'\n');
console.log(JSON.stringify(summary));
