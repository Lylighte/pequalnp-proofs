'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const zlib = require('node:zlib');
const crypto = require('node:crypto');
const source = path.join(__dirname, '../plane920-search/branch-game-four-orbits.gz');
const archive = zlib.gunzipSync(fs.readFileSync(source));
assert.equal(crypto.createHash('sha256').update(archive).digest('hex'),
  '3a6d9ef8b36ea45106becd8e592a4590fdd868cf3621e8113aa4e51fab75958e');
const raw = Array.from({length: 13}, (_, i) => [1<<i]);
function minimal(values) {
  const all = [...new Set(values)].sort((a,b) => a-b);
  return all.filter((a,i) => !all.slice(0,i).some(b => (a&b)===b));
}
const join = (a,b) => minimal([...a,...b]);
const meet = (a,b) => minimal(a.flatMap(x => b.map(y => x|y)));
const scope = a => a.reduce((s,v) => s|v,0);
function arm(point, parents, gates) {
  let a = point < 0 ? [0] : raw[point];
  for (let i=0;i<gates.length;i++) if (parents&(1<<i)) a=meet(a,gates[i]);
  return a;
}
function expand(mask,parts) {
  return parts.reduce((s,x) => s | (x&mask ? x : 0), 0);
}
function connect(a,b,parts) {
  const l=expand(scope(a),parts), r=expand(scope(b),parts);
  if(l&r) return null;
  return [...parts.filter(x => !(x&(l|r))),l|r];
}
function finalArms(gates) {
  const map=new Map();
  for(let p=-1;p<13;p++) for(let parents=0;parents<(1<<gates.length);parents++){
    if(p<0 && !parents) continue;
    const a=arm(p,parents,gates), mandatory=a.reduce((x,y)=>x&y,8191);
    if(mandatory&(mandatory-1)) continue;
    map.set(a.join(','),a);
  }
  return [...map.values()];
}
let failed=[0,0,0,0], surviving=[], completions=0, strictPassed=0;
const counts={};
const final=process.argv.includes('--five');
const privateTest=process.argv.includes('--private');
const fullTest=process.argv.includes('--full');
const privateOnly=process.argv.includes('--private-only');
const weighted=process.argv.includes('--weighted');
const late=process.argv.includes('--two-late')?require('./two-late.cjs'):null;
const lateSurvivors=[];
const closeLate=process.argv.includes('--close-late');
const required=closeLate?new Set(require('./two-late-results.json').lateSurvivors.map(r=>r[0]+','+r[1])):null;
const sixthWeights={},unresolvedSixth=[];
let latePrefixes=0;
const weights={};
const fullChecker=fullTest?require('./full-private.cjs'):null;
const tester=privateTest?require('./five-private.cjs'):null;
const privateResults={};
const priceHistogram={};
const live=[];
for(let pos=0;pos<archive.length;pos+=8) {
  const record=Array.from(archive.subarray(pos,pos+8)), gates=[], firstArms=[];
  let parts=raw.map(a=>a[0]);
  for(let i=0;i<4;i++){
    const [a,b]=record.slice(2*i,2*i+2).map(code=>arm((code>>3)-1,code&7,gates));
    parts=connect(a,b,parts);
    if(!parts){failed[i]++;break;}
    if(privateTest)firstArms.push([tester.signature(a),tester.signature(b)]);
    gates.push(join(a,b));
  }
  if(!parts)continue;
  surviving.push({orbit:pos/8,record,components:parts.filter(x=>x&(x-1))});
  if(!final)continue;
  const choices=finalArms(gates);
  const firstGates=privateTest?gates.map(tester.signature):[];
  const seen=new Set();
  let ordinal=0;
  for(let i=0;i<choices.length;i++)for(let j=0;j<i;j++){
    const a=choices[i],b=choices[j], merged=connect(a,b,parts);
    if(!merged)continue;
    const u=join(a,b), key=u.join(',');
    if(gates.some(v=>v.join(',')===key)||key===a.join(',')||key===b.join(','))continue;
    completions++;
    seen.add(key);
    if(closeLate && required.has(pos/8+','+ordinal)){
      latePrefixes++;
      const prefix=[...gates,u],sixth=finalArms(prefix),earlier=prefix.map(tester.signature);
      for(let x=0;x<sixth.length;x++)for(let y=0;y<x;y++){
        const a6=sixth[x],b6=sixth[y];
        if(!connect(a6,b6,merged))continue;
        const f=join(a6,b6),label=f.join(',');
        if([a6,b6,...prefix].some(t=>t.join(',')===label))continue;
        const costs=fullChecker.check([...earlier,tester.signature(f)],0,6,true);
        const sum=costs.reduce((t,v)=>t+v,0);
        sixthWeights[sum]=(sixthWeights[sum]||0)+1;
        if(sum<=12)unresolvedSixth.push([pos/8,ordinal,x,y,costs]);
      }
    }
    if(privateTest){
      const cost=tester.bound([...firstGates,tester.signature(u)],
        [...firstArms,[tester.signature(a),tester.signature(b)]]);
      if(weighted){
        const costs=fullChecker.check([...firstGates,tester.signature(u)],0,8,true);
        const sum=costs.reduce((s,v)=>s+v,0);
        weights[sum]=(weights[sum]||0)+1;
        if(late){
          const failing=late.failure([...firstGates,tester.signature(u)],costs,6);
          if(failing)lateSurvivors.push([pos/8,ordinal,failing]);
        }
        cost.reason=sum>8?'privateOnly':'survives';
      }else if(privateOnly){
        cost.reason=fullChecker.check([...firstGates,tester.signature(u)],0)?'survives':'privateOnly';
      }else if(fullTest && cost.reason==='survives' &&
          !fullChecker.check([...firstGates,tester.signature(u)],cost.shared))cost.reason='fullBudget';
      privateResults[cost.reason]=(privateResults[cost.reason]||0)+1;
      if(cost.reason!=='dominated'){
        const label=cost.privateTotal+','+cost.shared;
        priceHistogram[label]=(priceHistogram[label]||0)+1;
      }
      if(cost.reason==='survives')live.push([pos/8,i,j,cost.privateTotal,cost.shared,ordinal]);
    }
    ordinal++;
  }
  strictPassed+=seen.size;
  counts[seen.size]=(counts[seen.size]||0)+1;
}
assert.equal(surviving.length+failed.reduce((a,b)=>a+b,0),1217);
const result={failed,surviving:surviving.length,final,completions,distinctFunctionsPerPrefix:strictPassed,counts};
if(privateTest){
  if(closeLate)fs.writeFileSync(path.join(__dirname,'sixth-late-results.json'),JSON.stringify({latePrefixes,sixthWeights,unresolvedSixth})+'\n');
  if(weighted)fs.writeFileSync(path.join(__dirname,'five-weighted.json'),JSON.stringify(weights)+'\n');
  if(late)fs.writeFileSync(path.join(__dirname,'two-late-results.json'),JSON.stringify({total:completions,unresolved:lateSurvivors.length,lateSurvivors})+'\n');
  const filename=privateOnly?'five-only-private.json':fullTest?'five-full-private.json':'five-private.json';
  fs.writeFileSync(path.join(__dirname,filename),JSON.stringify({privateResults,priceHistogram,live})+'\n');
  console.log(privateResults);
}
fs.writeFileSync(path.join(__dirname,'or-forest'+(final?'-five':'')+'.json'),JSON.stringify({...result,prefixes:surviving},null,2)+'\n');
console.log(JSON.stringify(result));

