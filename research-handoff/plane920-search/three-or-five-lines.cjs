const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {perm,apply,weight:pc,lines}=require('../plane920-math/plane-orbits.js'),{inspect}=require('./private-independent.cjs');
const domain=Array.from({length:8192},(_,i)=>i).filter(m=>pc[m]<=4),univ=(1n<<BigInt(domain.length))-1n;
const raw=Array.from({length:13},(_,p)=>domain.reduce((w,m,j)=>w|((m&1<<p)?1n<<BigInt(j):0n),0n));
const loc=lines.map(m=>1n<<BigInt(domain.indexOf(m))),pm=w=>loc.reduce((v,t,j)=>v|((w&t)?1<<j:0),0);
const prime=ts=>[...new Set(ts)].sort((a,b)=>a-b).filter((v,i,s)=>!s.slice(0,i).some(b=>(v&b)===b));
const mult=(x,y)=>prime(x.flatMap(a=>y.map(b=>a|b))),join=(x,y)=>prime([...x,...y]);
const rel=(x,p)=>x.map(m=>apply(m,p)).sort((a,b)=>a-b).join(',');
const tableMemo=new Map();
function table(t){
 const k=t.join(',');if(tableMemo.has(k))return tableMemo.get(k);
 const v=domain.reduce((s,m,j)=>s|(t.some(a=>(a&m)===a)?1n<<BigInt(j):0n),0n);tableMemo.set(k,v);return v;
}
function next(old,mustShare=false){
 const arms=new Map(),family=new Map(),prev=new Set(old.map(t=>t.join(',')));
 for(let p=-1;p<13;p++)for(let j=0;j<1<<old.length;j++){
   if(p===-1&&!j)continue;let t=[p===-1?0:1<<p];
   for(let k=0;k<old.length;k++)if(j&1<<k)t=mult(t,old[k]);
   if(pc[t.reduce((m,x)=>m&x,8191)]>1)continue;
   if(mustShare&&!(t.length===1&&pc[t[0]]===1)&&!prev.has(t.join(','))&&lines.filter(L=>t.some(q=>(q&L)===q)).length<2)continue;
   arms.set(t.join(','),t);
 }
 const list=[...arms.values()];
 for(let i=0;i<list.length;i++)for(let j=0;j<i;j++){
   const a=list[i],b=list[j],v=join(a,b),key=v.join(',');
   if(key===a.join(',')||key===b.join(',')||prev.has(key))continue;family.set(key,v);
 }
 return family;
}
function orbits(family,g){
 const seen=new Set(),rs=[];
 for(const [key,t] of family){
   if(seen.has(key))continue;const stab=[],orbit=new Set();
   for(const p of g){const v=rel(t,p);assert(family.has(v));orbit.add(v);seen.add(v);if(v===key)stab.push(p);}
   assert.equal(stab.length*orbit.size,g.length);rs.push({t,stab,size:orbit.size});
 }
 return rs;
}
function libraries(os,k,budget,lower,extra){
 const allProds=[univ];for(const o of os){const n=allProds.length;for(let i=0;i<n;i++)allProds.push(o&allProds[i]);}
 const named=new Set([...raw,...os,univ]),byRows=new Map();
 for(const a of [univ,...raw])for(const b of allProds){
   const w=a&b,S=pm(w);if(named.has(w)||pc[S]<2)continue;
   byRows.set(S,(byRows.get(S)??univ)&w);
 }
 const vs=[...byRows.values()].filter(w=>!named.has(w)),limit=budget-lower;
 if(limit===0 || limit<0)return null;
 const alive=vs.map(pm),choices=lines.map((L,i)=>{
   const pools=[];const push=(w,j)=>{if(w&loc[i])pools.push([w^loc[i],j]);};
   raw.forEach(w=>push(w,-1));os.forEach(w=>push(w,-1));vs.forEach(push);
   const two=new Set(),three=new Set();
   for(let a=0;a<pools.length;a++)for(let b=0;b<=a;b++){
     const [u,j]=pools[a],[v,l]=pools[b],tags=(j<0?0n:1n<<BigInt(j))|(l<0?0n:1n<<BigInt(l)),uv=u&v;
     if(!uv){two.add(tags);continue;}
     for(let c=0;c<b;c++){const [w,m]=pools[c];if(!(uv&w))three.add(tags|(m<0?0n:1n<<BigInt(m)));}
   }
   const reduce=s=>[...s].filter(t=>![...s].some(x=>x!==t&&(x&t)===x));
   return [reduce(two),reduce(new Set([...two,...three]))];
 });
 let winner;
 function go(start,left,tags,s){
   if(!left){
     const price=choices.map(([two,three])=>two.some(t=>(t&tags)===t)?0:three.some(t=>(t&tags)===t)?1:2);
     const total=price.slice().sort((a,b)=>a-b).slice(0,k).reduce((v,t)=>v+t,0)+s;
     if(total<=budget){
       const indices=vs.map((_,i)=>i).filter(i=>tags&1n<<BigInt(i));
       let set;
       if(extra){
         const usable=price.reduce((m,c,i)=>m|(c<=extra.maxPrivate?1<<i:0),0),ones=price.reduce((m,c,i)=>m|(c===1?1<<i:0),0);
         if(pc[usable]<k)return;
         for(let family=usable;family;family=(family-1)&usable){
           if(pc[family]!==k||pc[family&ones]+s>budget)continue;let ok=true;
           for(let sub=family;sub;sub=(sub-1)&family){
             const z=pc[sub];if(z>3)continue;
             const missing=indices.reduce((n,i)=>n+Number(!(alive[i]&sub)),0);
             if(budget-pc[(family^sub)&ones]-missing<[0,2,4,5][z]){ok=false;break;}
           }
           if(ok){set=family;break;}
         }
         if(!set)return;
       }
       winner={indices,positive:alive,price,total,family:set};
     }
     return;
   }
   for(let i=start;i+left<=vs.length&&!winner;i++)go(i+1,left-1,tags|1n<<BigInt(i),s);
 }
 // A real shared AND can narrow to an already-free atom. Charge one such
 // physical gate even when the distinct additional helper pool is empty.
 go(0,0,0n,1);
 for(let s=1;s<=limit&&!winner;s++)go(0,s,0n,s);
 return winner;
}
module.exports={next,orbits,table,libraries,prime,mult,join,raw,loc,lines,univ,pm,pc,rel,perm};
if(require.main===module){
const n=Number(process.argv[2]||3),k=Number(process.argv[3]||5),budget=Number(process.argv[4]||6),first=[1,2],stab=perm.filter(p=>rel(first,p)==='1,2');
assert.equal(stab.length,72);
const second=next([first]),two=orbits(second,stab),hist={},live=[],start=Date.now();let units=0,labeled=0,libTest=0;
function run(terms,weight){
 const ops=terms.map(table),{costs}=inspect(ops,100),min=costs.sort((a,b)=>a-b).slice(0,k).reduce((a,b)=>a+b);
 units++;labeled+=weight;hist[min]=(hist[min]||0)+1;
 if(min>=budget)return;
 libTest++;const witness=libraries(ops,k,budget,min);if(witness)live.push({terms,weight,witness});
}
for(const s of two){
 if(n===2)run([first,s.t],s.size);else{
   const family=next([first,s.t]);for(const t of orbits(family,s.stab))run([first,s.t,t.t],s.size*t.size);
 }
}
const summary={n,k,budget,secondFunctions:second.size,secondOrbits:two.length,orbits:units,labeledPerRoot:labeled,hist,libTest,survivors:live.length,ms:Date.now()-start};
fs.writeFileSync(path.join(__dirname,'few-or-'+[n,k,budget].join('-')+'.json'),JSON.stringify({summary,live})+'\n');console.log(summary);
}
