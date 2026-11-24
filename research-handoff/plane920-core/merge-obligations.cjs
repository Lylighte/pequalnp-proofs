'use strict';
const fs=require('node:fs'),path=require('node:path');
const n=13,F=(1<<n)-1;
const lines=Array.from({length:n},(_,i)=>[0,1,3,9].reduce((s,x)=>s|1<<((i+x)%n),0));
const pop=new Uint8Array(F+1);
for(let i=1;i<=F;i++)pop[i]=pop[i&(i-1)]+1;
const large=new Uint16Array(F+1);
for(let U=1;U<=F;U++) for(let i=0;i<n;i++) if(pop[lines[i]&U]>=2)large[U]|=1<<i;
const memo=new Map(), sizeStats={}, present=[];
function possible(U,hard){
 hard &= large[U];
 if(pop[U]<=2)return true;
 const key=U*8192+hard;
 if(memo.has(key))return memo.get(key);
 let ok=false;
 for(let A=(U-1)&U;A&&!ok;A=(A-1)&U){
   const B=U^A;
   if(A>B)continue;
   const cross=[];
   let hardCross=0, baseA=hard&large[A],baseB=hard&large[B];
   for(let i=0;i<n;i++) {
     const bit=1<<i,x=lines[i]&A,y=lines[i]&B;
     if(x&&y){cross.push({bit,x,y});if(bit&hard)hardCross|=bit;}
   }
   if(pop[hardCross]>1)continue;
   const h=cross.find(t=>t.bit&hardCross);
   const P=h?[h.x]:[0,...new Set(cross.map(t=>t.x))];
   const Q=h?[h.y]:[0,...new Set(cross.map(t=>t.y))];
   for(const p of P){if(ok)break;for(const q of Q){if(ok)break;
      let ha=baseA,hb=baseB;const choices=[];
      for(const {bit,x,y} of cross){
        const a=pop[x]>=2,b=pop[y]>=2;
        const dropA=!(bit&hard)&&q===y, dropB=!(bit&hard)&&p===x;
        if(a&&!dropA)ha|=bit;
        if(b&&!dropB)hb|=bit;
        if(a&&b&&dropA&&dropB)choices.push(bit);
      }
      for(let flip=0;flip<(1<<choices.length);flip++){
        let ca=ha,cb=hb;
        for(let j=0;j<choices.length;j++)if(flip&(1<<j))ca|=choices[j];else cb|=choices[j];
        if(possible(A,ca)&&possible(B,cb)){ok=true;break;}
      }
   }}
 }
 memo.set(key,ok);return ok;
}
const full=possible(F,0);
for(const [key,val] of memo){const k=pop[Math.floor(key/8192)]; const s=sizeStats[k]??={yes:0,no:0};s[val?'yes':'no']++;}
const result={full,checkedStates:memo.size,sizeStats};
fs.writeFileSync(path.join(__dirname,'merge-obligations.json'),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result));
