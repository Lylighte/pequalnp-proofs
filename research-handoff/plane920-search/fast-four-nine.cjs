const fs=require('node:fs'),path=require('node:path');
const {orbits,next,table,mult,raw,loc,lines,pc,perm,rel,univ,pm}=require('./three-or-five-lines.cjs'),{inspect}=require('./private-independent.cjs');
const {decompositions,pricedTables}=require('./paid-or-arms.cjs');
const initial=[1,2],st=perm.filter(p=>rel(initial,p)==='1,2'),seconds=orbits(next([initial],true),st),roots=[];
for(const a of seconds)for(const b of orbits(next([initial,a.t],true),a.stab))roots.push([initial,a.t,b.t]);
const from=Number(process.argv[2]||0),end=Math.min(roots.length,Number(process.argv[3]||roots.length)),start=Date.now();
const counts={from,end,pairs:0,undominated:0,screened:0,prefixTests:0,weakFamilies:0,charging:0,live:[]};
for(let ix=from;ix<end;ix++){
 const gs=roots[ix],flags=gs.map(table),named=new Set([...raw,...flags]),base=decompositions(gs).map(z=>z.map(table));
 const glob=flags.map(pm); const products=[univ];for(const g of flags)for(const a of [...products])products.push(a&g);
 const pools=new Map(),cache=new Map();
 for(let p=-1;p<13;p++)for(let j=0;j<8;j++){
  if(p<0&&!j)continue;const v=products[j]&(p<0?univ:raw[p]);if(pools.has(v))continue;
  const alive=pm(v);if(pc[alive]<2)continue;
  // Any eligible arm is true on two selected lines, hence cannot force two raw points.
  pools.set(v,{v,alive,p,j});
 }
 const arms=[...pools.values()],good=Array.from({length:13},()=>new Uint8Array(arms.length));let old=0;
 for(let l=0;l<13;l++){
  const f=flags.reduce((w,g)=>(g&loc[l])?w&g:w,univ),bad=[];
  for(let q=lines[l];q;q=(q-1)&lines[l])if(pc[q]===3)bad.push((table([q])&f)^loc[l]);
  if(bad.includes(0n))old|=1<<l;
  for(let a=0;a<arms.length;a++)good[l][a]=bad.reduce((m,x,k)=>m|(!(x&arms[a].v)?1<<k:0),0);
 }
 for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
  counts.pairs++;const a=arms[i],b=arms[j],x=a.alive&~b.alive,y=b.alive&~a.alive;
  if(!x||!y)continue;counts.undominated++;const s=a.alive|b.alive;
  let usable=old;for(let v=s&~old;v;v&=v-1){const z=Math.log2(v&-v);if(good[z][i]&good[z][j])usable|=1<<z;}
  if(pc[usable]<6)continue;
  const u=a.v|b.v;if(named.has(u))continue;counts.screened++;
  let data=cache.get(u);if(!data){
   const costs=inspect([...flags,u],100).costs;const ok=costs.reduce((m,c,z)=>m|(c<=1?1<<z:0),0),ones=costs.reduce((m,c,z)=>m|(c===1?1<<z:0),0);
   const fams=[];for(let m=ok;m;m=(m-1)&ok)if(pc[m]===6)fams.push([m,pc[m&ones]]);
   data={fams,ones};cache.set(u,data);
  }
  const full=[...flags,u],cuts=[...flags.flatMap(g=>[pm(g),pm(g)]),x,y];
  for(const fixed of base){
   const paid=[...new Set([...fixed,...[a.v,b.v].filter(z=>!named.has(z))])],pos=paid.map(pm);
   counts.prefixTests++;
   for(const [fam,c] of data.fams){
    if(c+paid.length>9||!(fam&x)||!(fam&y)||pos.some(t=>pc[t&fam]<2))continue;
    counts.weakFamilies++;
    // Every already counted private vanishes outside its own line, and each
    // actual mandatory paid arm is shared on this family. Stronger subcases
    // apply if an OR can be bypassed after restriction to J.
    let ok=true;
    for(let sub=fam;sub;sub=(sub-1)&fam){
     const n=pc[sub];let e=0;
     for(let z=0;z<3;z++)if(pc[glob[z]&sub]>=2)e++;
     if((sub&x)&&(sub&y))e++;
     let need=[0,2,4,5,5,5,6][n];if(e<=4&&n>=5)need=n===5?8:9;if(e<=3&&n>=3)need=2*n-1;if(e<=1)need=2*n;
     if(pc[(fam^sub)&data.ones]+pos.filter(t=>!(t&sub)).length+need>9){ok=false;break;}
    }
    if(!ok)continue;counts.charging++;
    const r=pricedTables(full,paid,6,9,fam,1,cuts,true);
    if(r.found)counts.live.push({ix,gs,a:[a.p,a.j],b:[b.p,b.j],fam,paid:paid.map(v=>v.toString(16)),r});
   }
  }
 }
}
counts.ms=Date.now()-start;fs.writeFileSync(path.join(__dirname,'fast-four-nine-'+from+'-'+end+'.json'),JSON.stringify(counts)+'\n');
console.log({...counts,live:counts.live.length});
