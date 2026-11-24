const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const lines=Array.from({length:13},(_,i)=>[i,(i+1)%13,(i+3)%13,(i+9)%13]);
for(let i=0;i<13;i++)for(let j=0;j<i;j++)assert.equal(lines[i].filter(p=>lines[j].includes(p)).length,1);
function combos(n,k,first=0){
 if(!k)return [[]];const a=[];
 for(let i=first;i<n;i++)for(const r of combos(n,k-1,i+1))a.push([i,...r]);return a;
}
function permutations(values){
 if(!values.length)return [[]];
 return values.flatMap((v,i)=>permutations(values.filter((_,j)=>j!==i)).map(a=>[v,...a]));
}
function signature(ids){
 return permutations(ids).map(seq=>{
   const hist=new Uint8Array(1<<ids.length);
   for(let p=0;p<13;p++){let label=0;for(const i of seq)label=2*label+Number(lines[i].includes(p));hist[label]++;}
   return [...hist].join(',');
 }).sort()[0];
}
function orbits(k,reps){
 const types=new Map(reps.map(r=>[signature(r),{r,n:0}]));
 for(const t of combos(13,k)){const c=types.get(signature(t));assert(c);c.n++;}
 return [...types.values()];
}
const chosen=[];
for(const k of [2,3,4,5])for(const p of combos(7,k))chosen.push(p.reduce((n,i)=>n+2**i,0));
chosen.sort((a,b)=>a-b);const sums=[];
for(const name of ['quadrilateral-complete','three-concurrent-plus-fourth-complete']){
 const r=require('./'+name+'.json');assert.deepEqual(r.complete.map(x=>x.ops).sort((a,b)=>a-b),chosen);
 sums.push({name,distinctMasks:new Set(r.complete.map(x=>x.ops)).size});
}
const report={triples:orbits(3,[[0,1,2],[0,1,5]]),quadruples:orbits(4,[[0,1,2,4],[0,1,2,5],[0,1,5,11]]),sums};
fs.writeFileSync(path.join(__dirname,'local-pattern-audit.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report));
