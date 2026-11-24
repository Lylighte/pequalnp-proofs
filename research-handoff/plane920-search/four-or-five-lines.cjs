const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {orbits,next,table,prime,mult,join,raw,loc,lines,univ,pm,pc,perm,rel}=require('./three-or-five-lines.cjs'),{inspect}=require('./private-independent.cjs');
const first=[1,2],rootStab=perm.filter(p=>rel(first,p)==='1,2'),root2=orbits(next([first]),rootStab);
const list=[];
for(const s of root2)for(const t of orbits(next([first,s.t]),s.stab))list.push([first,s.t,t.t]);
assert.equal(list.length,4483);
const badOffers={};
function enumerate(terms){
 const v=terms.map(table),positive=v.map(pm),pool=new Map(),oprod=[univ];
 for(const g of v){const m=oprod.length;for(let j=0;j<m;j++)oprod.push(oprod[j]&g);}
 for(let p=-1;p<13;p++)for(let J=0;J<8;J++){
   if(p<0&&!J)continue;
   let t=p<0?[0]:[1<<p];for(let j=0;j<3;j++)if(J&1<<j)t=mult(t,terms[j]);
   if(pc[t.reduce((a,b)=>a&b,8191)]>1)continue;
   const w=oprod[J]&(p<0?univ:raw[p]);
   pool.set(t.join(','),{p,J,t,w,pos:pm(w),good:[],allowed:[]});
 }
 const arms=[...pool.values()],dynamic=[];
 let fixed=false,baseline=0;
 for(let l=0;l<13;l++){
    const opts=new Map();
    for(let j=0;j<13;j++)if(j!==l){
      const p=31-Math.clz32(lines[l]&lines[j]),both=v.reduce((m,g,i)=>m|((positive[i]&1<<l)&&(positive[i]&1<<j)?1<<i:0),0);
      const w=raw[p]&oprod[both];opts.set(w,(opts.get(w)||0)|1<<j);
    }
    for(let j=0;j<3;j++)if(positive[j]===1<<l)opts.set(v[j],opts.get(v[j])||0);
    const previous=[...opts],strong=previous.map(([w,m])=>[w^loc[l],m]);
    const any=strong.some(([a])=>strong.some(([b])=>!(a&b)));
    if(any){baseline|=1<<l;continue;}
    // A fourth OR used as its own terminal input is always legal at its
    // positive rows. Otherwise it strengthens precisely the marked factors.
    strong.push([univ^loc[l],8191]);
    const d=new Map();
    for(let i=0;i<strong.length;i++)for(let j=0;j<=i;j++){
      const [a,m]=strong[i],[b,n]=strong[j],bad=a&b,mark=m|n;
      if(mark)d.set(bad,(d.get(bad)||0)|mark);
    }
    const ds=[...d],idx=dynamic.length;dynamic.push(l);
    for(const a of arms){
      let good=0n,activate=0n,index=1n;
      for(const [b,m] of ds){
        if(!(b&a.w))good|=index;
        if(m&a.pos)activate|=index;
        index<<=1n;
      }
      a.good[idx]=good;a.allowed[idx]=activate;
    }
 }
 return {arms,dynamic,baseline,v};
}
const from=Number(process.argv[2]||0),to=Math.min(list.length,Number(process.argv[3]||list.length)),out=path.join(__dirname,'four-or-five-'+from+'-'+to+'.json'),start=Date.now(),live=[];
let rawPairs=0,fourZero=0,actual=0;
for(let off=from;off<to;off++){
 const terms=list[off],{arms,dynamic,baseline,v}=enumerate(terms),fixed=pc[baseline],seen=new Set();
 for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
   const a=arms[i],b=arms[j],pos=a.pos|b.pos;rawPairs++;
   if(pos===a.pos||pos===b.pos)continue;
   let zero=fixed;
   for(let k=0;k<dynamic.length;k++)if(pos&1<<dynamic[k]){
     if(a.good[k]&b.good[k]&(a.allowed[k]|b.allowed[k]))zero++;
   }
   if(zero<4)continue;fourZero++;
   const w=a.w|b.w;if(seen.has(w))continue;seen.add(w);
   const costs=inspect([...v,w],100).costs;
   assert.equal(costs.filter(c=>c===0).length,zero);
   const m=costs.slice().sort((x,y)=>x-y).slice(0,5).reduce((x,y)=>x+y);
   if(m<=1){actual++;live.push({off,t:terms,a:[a.p,a.J],b:[b.p,b.J],costs});}
 }
}
const summary={from,to,rawPairs,fourZero,actual,ms:Date.now()-start};
fs.writeFileSync(out,JSON.stringify({summary,live})+'\n');console.log(summary);
