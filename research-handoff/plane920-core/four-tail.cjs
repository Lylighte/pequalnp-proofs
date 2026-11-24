'use strict';
const assert=require('node:assert/strict'),path=require('node:path'),fs=require('node:fs');
const {can,join}=require('./unrestricted-prefix.cjs');
const branches=require('../plane920-search/branch-game-three.json');
const programs=[];
function trees(available,steps){
  if(available.length===1){programs.push(steps);return;}
  for(let i=0;i<available.length;i++)for(let j=0;j<i;j++){
    const rest=available.filter((_,k)=>k!==i&&k!==j);
    trees([...rest,13+steps.length],[...steps,[available[j],available[i]]]);
  }
}
for(let l=0;l<13;l++)trees([0,1,3,9].map(x=>(x+l)%13),[]);
assert.equal(programs.length,branches.verifiedCritical);
const facts=[];
const counts=(process.argv[2]||'4').split(',').map(Number);
for(const total of [27,28,29,30])for(const h of counts){
  const live=[];
  for(const [index,program] of programs.entries()){
    const pool=Array.from({length:13},(_,i)=>[1<<i]),gs=[],pairs=[];
    for(const [a,b] of program){const pair=[pool[a],pool[b]],g=join(...pair);gs.push(g);pairs.push(pair);pool.push(g);}
    if(can(gs,pairs,[h],total).length)live.push(index);
  }
  facts.push({total,h,cases:programs.length,unresolved:live.length});
}
assert.equal(facts[0].cases,234);
fs.writeFileSync(path.join(__dirname,'four-tail'+(counts.length===1&&counts[0]===4?'':'-'+counts.join(''))+'.json'),JSON.stringify(facts)+'\n');
console.log(facts);

