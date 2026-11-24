const fs=require('node:fs'),path=require('node:path'),zlib=require('node:zlib'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const {prime,table,lines,pc,pm,raw}=require('./three-or-five-lines.cjs'),{inspect}=require('./private-independent.cjs');
const dir=path.join(__dirname,'../plane920-core/unrestricted'),full=8191,source=zlib.gunzipSync(fs.readFileSync(path.join(__dirname,'branch-game-four-orbits.gz')));
assert.equal(crypto.createHash('sha256').update(source).digest('hex'),'3a6d9ef8b36ea45106becd8e592a4590fdd868cf3621e8113aa4e51fab75958e');
const signed=new Map(),rawKeys=new Set(raw.map((_,i)=>String(1<<i))),rawS=[full,0,...raw.map(pm),...lines.map((_,i)=>1<<i)];
const columns=Array(8192);columns[0]=(1n<<1093n)-1n;
for(let m=1;m<=full;m++)columns[m]=columns[m&(m-1)]&raw[31-Math.clz32(m&-m)];
function wire(t){
 const key=t.join(',');if(!signed.has(key)){const m=t.reduce((p,x)=>p&x,full),positive=lines.reduce((v,L,i)=>v|(t.some(x=>(x&L)===x)?1<<i:0),0);
   signed.set(key,{key,t,m,positive,w:t.reduce((v,n)=>v|columns[n],0n)});}
 return signed.get(key);
}
function productTable(gs){
 const ps=[[0]];for(const g of gs)for(const a of [...ps])ps.push(prime(a.flatMap(x=>g.t.map(y=>x|y))));return ps;
}
function code(p,J,ps){const r=p<0?0:1<<p;return wire(prime(ps[J].map(x=>x|r)));}
function base(id){
 const gs=[],ps=[];for(let j=0;j<4;j++){
   const pd=productTable(gs),q=Array.from(source.subarray(8*id+2*j,8*id+2*j+2)).map(k=>code((k>>3)-1,k%8,pd));
   gs.push(wire(prime([...q[0].t,...q[1].t])));ps.push(q);
 }
 return {gs,ps};
}
function expand(gs,ps,visit,needFunction=true){
 const pd=productTable(gs),set=new Map();for(let p=-1;p<13;p++)for(let J=0;J<pd.length;J++){
   if(p<0&&!J)continue;const w=code(p,J,pd);if(pc[w.m]>1)continue;set.set(w.key,w);
 }
 const arms=[...set.values()],old=new Set(gs.map(a=>a.key));let n=0;
 for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
   const a=arms[i],b=arms[j];if(!(a.positive&~b.positive)||!(b.positive&~a.positive))continue;
   const g=wire(prime([...a.t,...b.t]));if(old.has(g.key))continue;
   n++;if(needFunction)visit([...gs,g],[...ps,[a,b]],i,j);
 }
 return n;
}
function features(gs,ps){
 const names=new Set(rawKeys),forced=new Map(),floor=Array(13).fill(0);
 for(let j=0;j<gs.length;j++){
   const [a,b]=ps[j];if(!(a.positive&~b.positive)||!(b.positive&~a.positive))return null;
   for(const z of [a,b])if(!names.has(z.key))forced.set(z.key,z.positive);
   names.add(gs[j].key);
 }
 let shared=0;for(const m of forced.values())if(pc[m]===1)floor[31-Math.clz32(m)]++;else shared++;
 const cost=inspect(gs.map(g=>g.w),100).costs,charges=cost.map((c,i)=>Math.max(c,floor[i])),sumFloor=floor.reduce((a,b)=>a+b,0);
 const delta=charges.map((c,i)=>c-floor[i]),one=delta.reduce((m,x,i)=>m|(x>=1?1<<i:0),0),two=delta.reduce((m,x,i)=>m|(x>=2?1<<i:0),0);
 const masks=new Set(rawS);for(const g of gs)for(const s of [...masks])masks.add(g.positive&s);
 const sg=[...masks];
 const ranked=charges.map((x,i)=>[x,i]).sort((a,b)=>a[0]-b[0]);
 return (h)=>{
   const hidden=14-h,limit=hidden-shared-sumFloor,memo=new Map(),fits=new Map();
   function leaf(s){
     if(fits.has(s))return fits.get(s);
     const w=pc[s&one]+pc[s&two];let ok=w<=limit;
     if(ok&&shared===0&&w===limit&&2*pc[s]>hidden)ok=false;
     if(ok){
       let r=0,added=0;
       for(const [x,i] of ranked)if(s&1<<i){
          added+=x;r++;if(w+sumFloor-added+[0,2,4,5][r]>hidden){ok=false;break;}if(r===3)break;
       }
     }
     fits.set(s,ok);return ok;
   }
   function go(s,d){
     if(leaf(s))return true;
     if(d===0||pc[s&one]+pc[s&two]>limit*(1<<d))return false;
     const key=s*4+d;if(memo.has(key))return memo.get(key);
     const solve=()=>{
       if(d>=2&&go(s,d-1))return true;
       const candidates=sg.filter(a=>go(s&~a,d-1));
       for(let i=1;i<candidates.length;i++)for(let j=0;j<i;j++){
         const a=candidates[i],b=candidates[j],x=s&~(a&~b),y=s&~(b&~a);
         if(x!==s&&y!==s&&go(x,d-1)&&go(y,d-1))return true;
       }
       return false;
     };const v=solve();memo.set(key,v);return v;
   }
   return go(full,h-gs.length);
 };
}
const rr=new Map(),later=new Map();
for(const n of fs.readdirSync(dir).filter(x=>/^round-27-5678-.*\.jsonl$/.test(x)))for(const t of fs.readFileSync(path.join(dir,n),'utf8').trim().split('\n')){
 const z=JSON.parse(t);assert(!rr.has(z.id));rr.set(z.id,z);
}
for(const t of fs.readFileSync(path.join(dir,'sixth-27-7.jsonl'),'utf8').trim().split('\n')){const z=JSON.parse(t);assert(!later.has(z.id));later.set(z.id,z);}
assert.equal(rr.size,1217);assert.equal(later.size,1217);
const begin=Number(process.argv[2]||0),end=Number(process.argv[3]||1217),summary={begin,end,active:[0,0,0],fifths:0,examinedFifth:0,late:[0,0,0],sixths:0,unresolved:0},start=Date.now();
for(let id=begin;id<end;id++){
 signed.clear();
 const r=rr.get(id),s=later.get(id),{gs,ps}=base(id),f=features(gs,ps),active=f?[5,6,7].filter(f):[];
 assert.deepEqual(active,r.active.filter(h=>h<=7));active.forEach(h=>summary.active[h-5]++);
 if(!r.active.length){assert.equal(r.fifth,0);continue;}
 const expected=r.live.map(([i,j,h])=>[i,j,h.filter(x=>x<=7)]).filter(a=>a[2].length),received=[];
 const sixth=new Map(s.runs.map(e=>[[e.i,e.j].join(','),e]));
 const number=expand(gs,ps,(g,p,i,j)=>{
   summary.examinedFifth++;const a=features(g,p),hs=a?active.filter(a):[];if(!hs.length)return;
   received.push([i,j,hs]);hs.forEach(h=>summary.late[h-5]++);
   if(hs.includes(7)){
     const line=sixth.get([i,j].join(','));assert(line);const survive=[];
     const n=expand(g,p,(gg,pp,u,v)=>{const test=features(gg,pp);if(test&&test(7))survive.push([u,v]);});
     assert.deepEqual(survive,line.unresolved);assert.equal(n,line.checked);summary.sixths+=n;summary.unresolved+=survive.length;
   }
 },active.length>0);
 assert.equal(number,r.fifth);summary.fifths+=number;assert.deepEqual(received,expected);assert.equal(sixth.size,received.filter(x=>x[2].includes(7)).length);
}
summary.ms=Date.now()-start;fs.writeFileSync(path.join(__dirname,'audit-27-low-'+begin+'-'+end+'.json'),JSON.stringify(summary)+'\n');console.log(summary);
