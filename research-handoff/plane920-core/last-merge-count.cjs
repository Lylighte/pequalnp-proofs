'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const full=8191, lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,x)=>m|1<<((x+i)%13),0));
const pc=new Uint8Array(full+1);
for(let i=1;i<=full;i++) pc[i]=pc[i&(i-1)]+1;
const hist={}, examples={};
for(let A=1;A<full;A++){
  const B=full^A,a=pc[A],b=pc[B];
  if(a>b || (a===b&&A>B)) continue;
  const crossing=lines.filter(L=>(L&A)&&(L&B));
  const cells=crossing.map(L=>[L&A,L&B]);
  const possibleA=[0,...new Set(cells.map(([x])=>x))];
  const possibleB=[0,...new Set(cells.map(([,y])=>y))];
  let best=100;
  for(const P of possibleA)for(const Q of possibleB){
    let ca=0,cb=0,maxSave=0;
    for(const [x,y] of cells){
      const wa=pc[x]-1,wb=pc[y]-1;
      ca+=wa;cb+=wb;
      // If an exceptional use of H avoids the normal A-side signal, the fixed B-side driver must have unique minimum y=Q. Conversely for B.
      const saveA=Q===y?wa:0,saveB=P===x?wb:0;
      maxSave+=Math.max(saveA,saveB);
    }
    const normal=ca+cb;
    // No H is needed for the full accounting in the normal case. If any exceptional case is used, H is itself a hidden AND.
    const lower=Math.min(normal,1+normal-maxSave);
    best=Math.min(best,lower);
  }
  const key=a+'/'+b;(hist[key]??={})[best]=((hist[key]??{})[best]||0)+1;
  if(best<=7)(examples[key]??=[]).push(A);
}
const out={hist,possibleCutsAtSevenHiddenAnds:examples};
fs.writeFileSync(path.join(__dirname,'last-merge-count.json'),JSON.stringify(out,null,2)+'\n');
console.log(JSON.stringify(hist));
