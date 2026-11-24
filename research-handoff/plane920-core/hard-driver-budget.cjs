'use strict';

const fs=require('node:fs'),path=require('node:path');
const full=8191;
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((s,x)=>s|1<<((x+i)%13),0));
const pop=new Uint8Array(full+1), large=new Uint16Array(full+1);
for(let m=1;m<=full;m++)pop[m]=pop[m>>1]+(m&1);
for(let m=1;m<=full;m++)for(let i=0;i<13;i++)if(pop[m&lines[i]]>=2)large[m]|=1<<i;
const coarse=JSON.parse(fs.readFileSync(path.join(__dirname,'merge-all-slices.json'),'utf8')).bySize;
const coarseMin=[0,...Array.from({length:13},(_,k)=>Math.min(...Object.keys(coarse[k+1]).map(Number)))];

function lower(U,h){
 let cost=0;
 for(let i=0;i<13;i++)if(h & (1<<i))cost+=Math.max(0,pop[U&lines[i]]-1);
 return Math.max(cost,coarseMin[pop[U]]);
}
const memo=new Map(),stats={}; const bonus=Number(process.argv[3]||0);
function minOr(masks) {
 const sets=[...new Set(masks)];let best=0;
 for(let m=1;m<(1<<sets.length);m++){if(pop[m]<=best)continue;let used=0,ok=true;
 for(let j=0;j<sets.length;j++)if(m&(1<<j)){if(sets[j]&used){ok=false;break;}used|=sets[j];}
 if(ok)best=pop[m];}return Math.max(0,best-1);
}

function possible(U,h,budget){
 h &= large[U];
 if(lower(U,h)>budget)return false;
 if(pop[U]<=2)return true;
 const key=(U*8192+h)*16+budget;
 if(memo.has(key))return memo.get(key);
 let ok=false;
 for(let A=(U-1)&U;A&&!ok;A=(A-1)&U){
   const B=U^A;
   if(A>B || coarseMin[pop[A]]+coarseMin[pop[B]]>budget)continue;
   const cells=[];
   let hardCross=0;
   for(let i=0;i<13;i++){
     const x=lines[i]&A,y=lines[i]&B,bit=1<<i;
     if(x&&y){cells.push({x,y,bit});hardCross|=h&bit;}
   }
   if(pop[hardCross]>1)continue;
   function children(ha,hb,cost,ora=0,orb=0){
     const na=lower(A,ha),nb=lower(B,hb); if(na+ora>pop[A]-1+bonus||nb+orb>pop[B]-1+bonus||na+nb+ora+orb>pop[A]+pop[B]-2+bonus)return false;
     for(let ba=na;ba<=Math.min(pop[A]-1,budget-cost-nb);ba++){
       const bb=Math.min(pop[B]-1,budget-cost-ba);
       if(possible(A,ha,ba)&&possible(B,hb,bb))return true;
     }
     return false;
   }
   let allA=h&large[A],allB=h&large[B];
   for(const {bit} of cells){allA|=bit&large[A];allB|=bit&large[B];}
   if(!hardCross&&children(allA,allB,0)){ok=true;break;}
   const hardCell=cells.find(t=>t.bit&hardCross);
   const P=hardCell?[hardCell.x]:[0,...new Set(cells.map(c=>c.x))];
   const Q=hardCell?[hardCell.y]:[0,...new Set(cells.map(c=>c.y))];
   for(const p of P){if(ok)break;for(const q of Q){if(ok)break;
     let ha=h&large[A],hb=h&large[B];const opt=[],forced=[];
     for(const c of cells){
       const {x,y,bit}=c;
       const da=!(bit&h)&&q===y&&pop[x]>=2,db=!(bit&h)&&p===x&&pop[y]>=2;
       if(!da)ha|=bit&large[A];if(!db)hb|=bit&large[B];
       if(bit&hardCross)forced.push(c);
       if(da||db)opt.push({...c,da,db});
     }
     function choices(j,aa,bb,uses,hasP,hasQ){
       if(ok || lower(A,aa)+lower(B,bb)+1>budget)return;
       if(j===opt.length){
         const all=forced.concat(uses);
         if((hasP||hardCross)&&all.some(c=>c.x!==p&&pop[c.x]<=pop[p]))return;
         if((hasQ||hardCross)&&all.some(c=>c.y!==q&&pop[c.y]<=pop[q]))return;
         if(children(aa,bb,1,minOr(all.map(c=>c.x)),minOr(all.map(c=>c.y))))ok=true;
         return;
       }
       const c=opt[j],la=c.bit&large[A],lb=c.bit&large[B];
       if(c.da) choices(j+1,aa,bb|lb,uses.concat(c),hasP,true);
       if(c.db) choices(j+1,aa|la,bb,uses.concat(c),true,hasQ);
       choices(j+1,aa|la,bb|lb,uses,hasP,hasQ);
     }
     choices(0,ha,hb,[],false,false);
   }}
 }
 memo.set(key,ok);return ok;
}
const max=Number(process.argv[2]||10);
const results=[];
for(let budget=7;budget<=max;budget++){
 const ok=possible(full,0,budget);results.push({budget,ok,memoSize:memo.size}); console.log(JSON.stringify(results.at(-1)));
 if(ok)break;
}
fs.writeFileSync(path.join(__dirname,'hard-driver-budget-'+bonus+'.json'),JSON.stringify(results,null,2)+'\n');
