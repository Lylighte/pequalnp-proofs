'use strict';

const fs=require('node:fs');
const path=require('node:path');
const assert=require('node:assert/strict');
const full=(1<<13)-1;
const weight=new Uint8Array(full+1);
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((s,v)=>s|1<<((v+i)%13),0));
const pencils=Array.from({length:13},(_,p)=>lines.reduce((s,L,i)=>s|((L & (1<<p))?1<<i:0),0));
const union=new Uint16Array(full+1);
for(let m=1;m<=full;m++){const bit=m&-m;weight[m]=1+weight[m^bit];union[m]=union[m^bit]|lines[31-Math.clz32(bit)];}

function run(budget){
  const result={budget,normalizedPointPair:[0,1],feasible:0,countByAnchorSize:{},examples:[]};
  const firstA=pencils[0],firstB=pencils[1];
  for(let anchor=1;anchor<=full;anchor++){
    const n=weight[anchor];
    if(39-2*n+2>budget) continue;
    const cap=new Int8Array(full+1);
    cap[0]=-100;
    for(let m=1;m<=full;m++) cap[m]=weight[union[m]]-weight[m & ~anchor];
    for(let i=0;i<13;i++)
      for(let m=0;m<=full;m++) if(m & (1<<i)) cap[m]=Math.max(cap[m],cap[m^(1<<i)]);
    if(12+cap[full]>budget) continue;
    for(const [A,B] of [[firstA,firstB&~firstA],[firstA&~firstB,firstB]]){
      const noFirst=[full^A,full^B];
      if(noFirst.some(mask=>13+cap[mask]>budget)) continue;
      // Mark the lines where the second OR selects a child that requires z.
      // The opposite child is allowed on every other line, a relaxation.
      let survived=false;
      for(let z=0;z<13 && !survived;z++){
        let S=pencils[z];
        for(;;){
          const noSecond=[S,full^S];
          if(noSecond.every(mask=>13+cap[mask]<=budget) &&
             noFirst.every(a=>noSecond.every(b=>14+cap[a&b]<=budget))){
            result.feasible++;
            result.countByAnchorSize[n]=(result.countByAnchorSize[n]||0)+1;
            if(result.examples.length<12)result.examples.push({anchor,A,B,z,S});
            survived=true;break;
          }
          if(!S)break;S=(S-1)&pencils[z];
        }
      }
      if(survived)break;
    }
  }
  return result;
}

const out=[24,25,26].map(run);
assert.equal(out[0].feasible,0);
const dir=__dirname;
fs.writeFileSync(path.join(dir,'anchor-deficit.json'),JSON.stringify(out,null,2)+'\n');
for(const r of out)console.log(JSON.stringify({budget:r.budget,patterns:r.feasible,countByAnchorSize:r.countByAnchorSize,example:r.examples[0]}));
