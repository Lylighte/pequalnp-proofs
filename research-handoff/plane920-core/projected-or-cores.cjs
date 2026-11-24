'use strict';
const fs=require('node:fs'),path=require('node:path');
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,x)=>m|1<<((i+x)%13),0));
const bits=m=>{let k=0;while(m){m&=m-1;k++;}return k;};
const hist={},max={},representative={};
for(let support=1;support<8192;support++){
 const size=bits(support);if(size<4||size>6)continue;
 let centers=0;
 for(let i=0;i<13;i++){
   const p=1<<i, available=support&~p;
   if(lines.every(L=>!(L&p)||(L&available)))centers|=p;
 }
 const count=bits(centers);(hist[size]??={})[count]=((hist[size]??{})[count]||0)+1;
 if(count>(max[size]??-1)){max[size]=count;representative[size]={support,centers};}
}
const s={hist,max,representative};
fs.writeFileSync(path.join(__dirname,'projected-or-cores.json'),JSON.stringify(s,null,2)+'\n');console.log(JSON.stringify(s));
