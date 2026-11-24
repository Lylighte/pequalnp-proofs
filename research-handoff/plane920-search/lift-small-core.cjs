const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {raw,table,pm,loc,pc}=require('./three-or-five-lines.cjs');
const {armOptions}=require('./paid-or-arms.cjs');
const cores=require('./three-line-five-cores.json'),results=[];
for(const record of cores)for(const helperList of record.out){
 const old=[...raw,...helperList.map(h=>BigInt('0x'+h)),table(record.row.firstOr),table(record.row.t)];
 const desc=Array(13).fill(null);
 for(let g=13;g<18;g++){
   const options=[];
   for(let i=0;i<20;i++)for(let j=0;j<i;j++){
     if(i===g||j===g||old[i]===old[g]||old[j]===old[g])continue;
     if((old[i]&old[j])===old[g])options.push([i,j,false]);
   }
   assert.equal(options.length,1);desc.push(options[0]);
 }
 desc.push([...record.row.firstOr.map(x=>old.indexOf(table([x]))),true],
           [old.indexOf(table(record.row.a)),old.indexOf(table(record.row.b)),true]);
 assert(desc.slice(13).every(([a,b])=>a>=0&&b>=0));
 const stats={source:record.i,templates:0,acyclic:0,activeRare:0,live:[]};
 for(let B=0;B<20;B++){
   const slots=[];for(let g=13;g<20;g++)for(let port=0;port<2;port++)if(desc[g][port]===B)slots.push([g,port]);
   for(let change=0;change<1<<slots.length;change++){
     const gates=desc.map(g=>g?[...g]:null);
     for(let k=0;k<slots.length;k++)if(change&1<<k){const [g,port]=slots[k];gates[g][port]=21;}
     for(let i=0;i<20;i++)for(let j=0;j<i;j++){
       stats.templates++;
       gates[20]=[i,j,false];gates[21]=[B,20,true];
       const signal=[...raw],used=new Uint8Array(22);let cycle=false;
       function compute(g){
         if(signal[g]!==undefined)return signal[g];if(used[g]){cycle=true;return 0n;}
         used[g]=1;const [a,b,or]=gates[g],x=compute(a),y=compute(b);
         return signal[g]=or?x|y:x&y;
       }
       for(let g=13;g<22;g++)compute(g);if(cycle)continue;stats.acyclic++;
       const H=pm(signal[20]);if(H&7)continue;
       // An arm false on every new positive can also be dropped. A successful
       // original must use H on the added target and nowhere on the old three.
       if(!H)continue;stats.activeRare++;
       let covered=0;const pairs={};for(let a=0;a<22;a++)for(let b=0;b<=a;b++){
         const v=signal[a]&signal[b],tr=loc.indexOf(v);
         if(tr>=0){covered|=1<<tr;pairs[tr]=[a,b];}
       }
       const extra=covered&H&~7;if((covered&7)===7&&extra){
         stats.live.push({B,i,j,change,covered,extra,gates:gates.slice(13),pairs});
       }
     }
   }
 }
 results.push(stats);
}
fs.writeFileSync(path.join(__dirname,'lift-small-core.json'),JSON.stringify(results)+'\n');
console.log(results.map(({live,...s})=>({...s,survivors:live.length})));
