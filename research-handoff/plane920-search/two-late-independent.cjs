const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {runPrefix}=require('./surplus-fifth.cjs'),{inspect}=require('./private-independent.cjs'),forest=require('../plane920-core/or-forest-five.json'),{lines}=require('./branch-game.json');
const full=8191,count=Array.from({length:8192},(_,i)=>i.toString(2).replaceAll('0','').length),rows=Array.from({length:8192},(_,i)=>i).filter(m=>count[m]<=4);
const raw=Array.from({length:13},(_,p)=>rows.reduce((v,m,j)=>v|((m&1<<p)?1n<<BigInt(j):0n),0n)),all=(1n<<1093n)-1n;
const probes=lines.map(L=>1n<<BigInt(rows.indexOf(L)));
const positive=w=>probes.reduce((s,b,i)=>s|((w&b)?1<<i:0),0);
const stars=raw.map(positive),monomial=[0,full,...stars,...lines.map((_,i)=>1<<i)];
function survives(pos,costs){
 const one=costs.reduce((s,c,i)=>s|(c===1?1<<i:0),0),two=costs.reduce((s,c,i)=>s|(c===2?1<<i:0),0);
 const weight=m=>count[m&one]+2*count[m&two];
 const total=weight(full);
 if(total>24)return false;
 const sig=new Set(monomial);
 for(const p of pos)for(const m of [...sig])sig.add(m&p);
 const opts=[...sig],cache=new Map();
 function hasBadMove(rem,cap){
   const n=weight(rem);if(n<=cap)return true;if(n>2*cap)return false;
   const need=n-cap,reduced=[...new Set(opts.map(a=>a&rem).filter(a=>weight(a)>=need))];
   for(let i=0;i<reduced.length;i++)for(let j=0;j<i;j++){
     const a=reduced[i],b=reduced[j],ab=weight(a&b);
     if(weight(a)-ab>=need&&weight(b)-ab>=need)return true;
   }
   return false;
 }
 function bad(rem){if(!cache.has(rem))cache.set(rem,hasBadMove(rem,6));return cache.get(rem);}
 const need=total-12,first=opts.filter(w=>weight(w)>=need);
 for(let i=0;i<first.length;i++)for(let j=0;j<i;j++){
   const u=first[i],v=first[j],x=full&(~u|v),y=full&(~v|u);
   if(weight(x)<=12&&weight(y)<=12&&bad(x)&&bad(y))return true;
 }
 return false;
}
const prime=v=>[...new Set(v)].sort((a,b)=>a-b).filter((x,i,arr)=>!arr.slice(0,i).some(t=>(t&x)===t));
function extensions(gates,parts,cb){
 const products=[{t:[0],w:all}];
 for(const g of gates)for(const a of [...products])products.push({t:prime(a.t.flatMap(x=>g.terms.map(y=>x|y))),w:a.w&g.w});
 const arms=new Map();
 for(let p=-1;p<13;p++)for(let j=0;j<products.length;j++){
   if(p<0&&!j)continue;
   const d=products[j],t=prime(d.t.map(x=>x|(p<0?0:1<<p)));
   if(count[t.reduce((v,m)=>v&m,full)]>1)continue;
   const scope=t.reduce((v,m)=>v|m,0),comp=parts.reduce((v,r)=>v|(r&scope?r:0),scope);
   arms.set(t.join(','),{t,w:p<0?d.w:d.w&raw[p],comp});
 }
 const as=[...arms.values()],old=new Set(gates.map(g=>g.terms.join(',')));
 for(let i=0;i<as.length;i++)for(let j=0;j<i;j++){
   const a=as[i],b=as[j];if(a.comp&b.comp)continue;
   const key=prime([...a.t,...b.t]).join(',');if(old.has(key)||key===a.t.join(',')||key===b.t.join(','))continue;
   cb(a.w|b.w);
 }
}
const reference=require('../plane920-core/two-late-results.json'),ref6=require('../plane920-core/sixth-late-results.json'),ids=[],hist={},start=Date.now(),cache=new Map();
let programs=0,sixth=0;
for(const f of forest.prefixes)runPrefix(f,({orbit,number,a,b,e,ors})=>{
 programs++;const gates=[...ors,e],truth=gates.map(g=>g.w),costs=inspect(truth,100).costs,pos=truth.map(positive);
 const key=pos.join(',')+'/'+costs.join('');if(!cache.has(key))cache.set(key,survives(pos,costs));
 if(!cache.get(key))return;ids.push([orbit,number]);
 const merged=a.part|b.part,parts=[...f.components.filter(s=>!(s&merged)),merged];
 extensions(gates,parts,w=>{const total=inspect([...truth,w],100).total;hist[total]=(hist[total]||0)+1;sixth++;});
});
assert.equal(programs,167922);assert.deepEqual(ids,reference.lateSurvivors.map(([o,n])=>[o,n]));assert.deepEqual(hist,ref6.sixthWeights);
const result={programs,cached:cache.size,remaining:ids,sixth,hist,ms:Date.now()-start,domain:rows.length};
fs.writeFileSync(path.join(__dirname,'two-late-independent.json'),JSON.stringify(result)+'\n');console.log({...result,remaining:ids.length});
