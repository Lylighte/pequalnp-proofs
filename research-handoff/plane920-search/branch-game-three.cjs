const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {lines}=require('./branch-game.json'),ALL=(1<<13)-1,pc=new Uint8Array(ALL+1);
for(let i=1;i<=ALL;i++)pc[i]=1+pc[i&(i-1)];
const star=Array.from({length:13},(_,v)=>lines.reduce((s,l,i)=>s+Number(!!(l&(1<<v)))*(1<<i),0));
const pairs=n=>Array.from({length:n},(_,b)=>Array.from({length:b},(_,a)=>[a,b])).flat();
const moves=[13,14,15].map(pairs),freq={},bad=[];
let total=0,min=13;
let verifiedCritical=0;
function sib(w,keep,a,b){
 return [[...w, w[a]],[...w,w[b]]].map((z,j)=>({w:z,keep:keep&~(w[j?a:b]&~w[j?b:a])}));
}
for(const a of moves[0]){
 const t1=sib(star,ALL,...a);
 for(const b of moves[1]){
   const t2=t1.flatMap(t=>sib(t.w,t.keep,...b));
   for(const c of moves[2]){
     let v=0;for(const z of t2){const x=z.w[c[0]],y=z.w[c[1]];
       v=Math.max(v,pc[z.keep&~(x&~y)],pc[z.keep&~(y&~x)]);}
     total++;freq[v]=(freq[v]||0)+1;min=Math.min(min,v);
     if(v<=4){
       const supp=Array.from({length:13},(_,i)=>1<<i),subtrees=[];
       for(const [i,j] of [a,b,c]){
         assert.equal(supp[i]&supp[j],0);
         const combined=supp[i]|supp[j];subtrees.push(combined);supp.push(combined);
       }
       assert(lines.includes(supp[15]));assert.equal(pc[supp[15]],4);
       for(const u of subtrees)for(const w of subtrees)assert((u&w)===0||(u&w)===u||(u&w)===w);
       verifiedCritical++;
       if(bad.length<3)bad.push([a,b,c]);
     }
   }
 }
}
const report={total,min,freq,bad,verifiedCritical};fs.writeFileSync(path.join(__dirname,'branch-game-three.json'),JSON.stringify(report,null,2)+'\n');console.log(report);
