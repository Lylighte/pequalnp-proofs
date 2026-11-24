const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {orbits,next,table,mult,raw,loc,lines,pc,perm,rel,univ,pm,libraries}=require('./three-or-five-lines.cjs'),{inspect}=require('./private-independent.cjs');
const five=process.argv.includes('--five'), nine=process.argv.includes('--nine'), familySize=five?5:6, budget=five?7:nine?9:8;
const mustShare=process.argv.includes('--shared-arms'),initial=[1,2],st=perm.filter(p=>rel(initial,p)==='1,2'),seconds=orbits(next([initial],mustShare),st);
const roots=[];for(const s of seconds)for(const q of orbits(next([initial,s.t],mustShare),s.stab))roots.push([initial,s.t,q.t]);
const from=Number(process.argv[2]||0),end=Math.min(roots.length,Number(process.argv[3]||roots.length)),start=Date.now(),hist={},survivors=[],sample=[],summary={from,end,allRoots:roots.length,tested:0,nonDominated:0,pass:0,unique:0,exactOK:0};
for(let which=from;which<end;which++){
 const gates=roots[which],w=gates.map(table),prods=[{t:[0],w:univ}];
 for(let i=0;i<3;i++)for(const z of [...prods])prods.push({t:mult(z.t,gates[i]),w:z.w&w[i]});
 const pool=new Map(),seen=new Set(),named=new Set(gates.map(t=>t.join(',')));
 for(let p=-1;p<13;p++)for(let j=0;j<8;j++){
   if(p<0&&!j)continue;const z=prods[j],t=p<0?z.t:mult(z.t,[1<<p]);
   if(pc[t.reduce((a,b)=>a&b,8191)]>1)continue;const v=z.w&(p<0?univ:raw[p]),pos=pm(v),key=t.join(',');
   if(mustShare&&pc[pos]<2&&!(t.length===1&&pc[t[0]]===1)&&!named.has(key))continue;
   pool.set(key,{v,pos,good:new Uint16Array(13),p,j,key});
 }
 const arms=[...pool.values()];let always0=0,always1=0;
 for(let i=0;i<13;i++){
   const point=raw.filter((_,p)=>lines[i]&1<<p),f=w.reduce((v,t)=>v&((t&loc[i])?t:univ),univ),bad=[];
   for(let a=0;a<4;a++)for(let b=0;b<a;b++)bad.push((f&point[a]&point[b])^loc[i]);
   for(let a=0;a<4;a++)bad.push(point.reduce((v,t,k)=>v&(k===a?univ:t),f)^loc[i]);
   if(bad.slice(0,6).includes(0n))always0|=1<<i;if(bad.slice(6).includes(0n))always1|=1<<i;
   for(const a of arms)for(let j=0;j<10;j++)if(!(bad[j]&a.v))a.good[i]|=1<<j;
 }
 for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
   summary.tested++;const a=arms[i],b=arms[j],pos=a.pos|b.pos;if(pos===a.pos||pos===b.pos)continue;summary.nonDominated++;
   let z=always0,o=always1;for(let m=0;m<13;m++)if(pos&1<<m){const hit=a.good[m]&b.good[m];if(hit&63)z|=1<<m;if(hit&960)o|=1<<m;}
   if(pc[o]<familySize)continue;summary.pass++;
   const u=a.v|b.v;if(seen.has(u))continue;seen.add(u);summary.unique++;
   const exact=inspect([...w,u],100).costs,low=exact.slice().sort((a,b)=>a-b);
   if(low[familySize-1]===2)continue;summary.exactOK++;const c=low.slice(0,familySize).reduce((a,b)=>a+b);
   hist[c]=(hist[c]||0)+1;
   const lib=libraries([...w,u],familySize,budget,c,{maxPrivate:1});if(lib)survivors.push({which,terms:gates,a:a.t??[a.p,a.j],b:b.t??[b.p,b.j],lib});
   if(sample.length<10)sample.push({which,i,j,c,exact});
 }
}
Object.assign(summary,{hist,survivors:survivors.length,ms:Date.now()-start});fs.writeFileSync(path.join(__dirname,(five?'four-or-5lines-7-':nine?'four-or-6lines-9-':'four-or-six-')+(mustShare?'shared-':'')+from+'-'+end+'.json'),JSON.stringify({summary,sample,survivors})+'\n');console.log(summary);
