const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const n=13,all=(1<<n)-1,lines=Array.from({length:n},(_,i)=>[0,1,3,9].reduce((m,v)=>m|1<<((i+v)%13),0));
const count=new Uint8Array(all+1);for(let m=1;m<=all;m++)count[m]=1+count[m&(m-1)];
// Signatures of every possible monomial, including the constant true. The
// constant false (and noncollinear monomials) has empty line signature.
const signatures=new Set([0,all]);
for(let a=0;a<=all;a++){
 let x=0;for(let i=0;i<n;i++)if((lines[i]&a)===a)x|=1<<i;
 signatures.add(x);
}
const sig=[...signatures].sort((a,b)=>a-b),moves=[];
for(let i=0;i<sig.length;i++)for(let j=0;j<i;j++){
 const a=sig[i],b=sig[j],x=a&~b,y=b&~a;
 if(x&&y)moves.push({a,b,x,y});
}
// A move whose two possible loss sets are contained in the two loss sets
// of another move can never improve the adversary's minimum.
const sub=(a,b)=>(a&b)===a;
const strong=moves.filter((a,i)=>!moves.some((b,j)=>i!==j&&
  ((sub(a.x,b.x)&&sub(a.y,b.y))||(sub(a.x,b.y)&&sub(a.y,b.x)))&&
  (count[b.x]+count[b.y]>count[a.x]+count[a.y])));
const hMax=25,history=[count],table=[];
for(let h=0;h<=hMax;h++){
 if(h){
  const prev=history.at(-1),cur=new Uint8Array(all+1);
  for(let s=0;s<=all;s++){
   let best=prev[s];
   for(const {x,y} of strong){
     const v=Math.max(prev[s&~x],prev[s&~y]);
     if(v<best)best=v;
   }
   cur[s]=best;
  }
  history.push(cur);
 }
 const k=history[h][all],hist=Array.from({length:14},()=>0);for(const v of history[h])hist[v]++;
 table.push({h,k,bound:13+2*k+h,hist});
}
// Re-evaluate the recurrence without domination pruning, for every state and
// attainable remaining-horizon layer, not just the full plane.
let checks=0;
for(let h=1;h<=hMax;h++){
 const prev=history[h-1],cur=history[h];
 for(let s=0;s<=all;s++){
   let w=prev[s];
   for(const a of sig)for(const b of sig){
     const u=Math.max(prev[s&(~a|b)],prev[s&(~b|a)]);
     if(u<w)w=u;
   }
   assert.equal(w,cur[s]);checks++;
 }
 if(Buffer.from(prev).equals(Buffer.from(cur)))break;
}
const data={lines,signatureCount:sig.length,signatureSizes:Object.fromEntries([0,1,4,13].map(k=>[k,sig.filter(s=>count[s]===k).length])),
  incomparablePairs:moves.length,maximalPairs:strong.length,checkedUnprunedStates:checks,table,
  layerHashes:history.map(m=>crypto.createHash('sha256').update(m).digest('hex'))};
fs.writeFileSync(path.join(__dirname,'branch-game.json'),JSON.stringify(data,null,2)+'\n');
console.log({signatures:sig.length,moves:moves.length,strong:strong.length,checks,table:table.map(r=>[r.h,r.k,r.bound])});
