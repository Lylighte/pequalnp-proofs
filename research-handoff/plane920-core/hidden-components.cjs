'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path');
const lines=Array.from({length:13},(_,w)=>[0,1,3,9].reduce((s,x)=>s|1<<((x+w)%13),0));
const incident=Array.from({length:13},(_,p)=>lines.map((line,i)=>line & (1<<p)?i:-1).filter(i=>i>=0));
const count=new Uint8Array(8192);for(let m=1;m<8192;m++)count[m]=count[m&(m-1)]+1;
const groups=[],paint=new Int16Array(13);
const stats={};
function visit(p){
 if(p===13){
   const k=groups.length;
   let crossing=0,distinctSignals=0;
   const targets=groups.map(()=>new Set());
   for(const L of lines){
     const pieces=groups.map(g=>g&L).filter(Boolean);
     if(pieces.length===2){crossing++;for(let j=0;j<k;j++)if(count[groups[j]&L]>=2)targets[j].add(groups[j]&L);}
   }
   let minHidden=0;
   for(let j=0;j<k;j++){distinctSignals+=targets[j].size;minHidden+=Math.max(targets[j].size,count[groups[j]]-1);}
   const tag=k+':'+groups.map(g=>count[g]).sort((a,b)=>b-a).join(',');
   const s=stats[tag]??={k,partitions:0,minCross:14,maxCross:0,minHidden:99,maxHidden:0};
   s.partitions++;s.minCross=Math.min(s.minCross,crossing);s.maxCross=Math.max(s.maxCross,crossing);
   s.minHidden=Math.min(s.minHidden,minHidden);s.maxHidden=Math.max(s.maxHidden,minHidden);
   return;
 }
 const used=groups.length;
 for(let c=0;c<=used;c++){
   const bit=1<<c;
   if(incident[p].some(i=>count[paint[i]|bit]>2))continue;
   const was=incident[p].map(i=>paint[i]);
   for(const i of incident[p])paint[i]|=bit;
   if(c===used)groups.push(1<<p);else groups[c]|=1<<p;
   visit(p+1);
   if(c===used)groups.pop();else groups[c]^=1<<p;
   for(let i=0;i<was.length;i++)paint[incident[p][i]]=was[i];
 }
}
visit(0);
const categories=Object.values(stats);
const summary={partitions:categories.reduce((a,b)=>a+b.partitions,0),maxComponents:Math.max(...categories.map(s=>s.k)),countsByK:{},categories:stats};
for(const s of categories)summary.countsByK[s.k]=(summary.countsByK[s.k]||0)+s.partitions;
assert.equal(summary.countsByK[2],4095);
fs.writeFileSync(path.join(__dirname,'hidden-components.json'),JSON.stringify(summary,null,2)+'\n');
console.log(JSON.stringify({partitions:summary.partitions,maxComponents:summary.maxComponents,counts:summary.countsByK}));
