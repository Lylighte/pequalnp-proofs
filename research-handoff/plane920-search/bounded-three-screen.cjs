const fs=require('node:fs'),path=require('node:path');
const {roots,rawProds}=require('./bounded-three-or.cjs'),{table,pc,pm,loc,lines,univ}=require('./three-or-five-lines.cjs');
const start=Date.now(),from=Number(process.argv[2]||0),end=Math.min(roots.length,Number(process.argv[3]||roots.length));
const counts={from,end,pairs:0,comparable:0,support:{},pass5:0,pass6:0},keep=[];
const triples=lines.map(L=>{const v=[];for(let s=L;s;s=(s-1)&L)if(pc[s]===3)v.push(table([s]));return v;});
for(let k=from;k<end;k++){
 const w=roots[k].map(table),prod=[univ,w[0],w[1],w[0]&w[1]],masks=prod.map(pm),map=new Map();
 for(const x of rawProds)for(let j=0;j<4;j++){
   if(!x.p&&!j)continue;const sign=x.s&masks[j];if(!sign)continue;
   const v=x.v&prod[j];if(!map.has(v))map.set(v,{v,sign,p:x.p,j,good:0n});
 }
 const arms=[...map.values()];let already=0;
 const good=Array.from({length:13},()=>new Uint8Array(arms.length));
 for(let l=0;l<13;l++){
   const f=w.reduce((v,g)=>(g&loc[l])?v&g:v,univ),bad=triples[l].map(t=>(t&f)^loc[l]);
   if(bad.includes(0n))already|=1<<l;
   for(let i=0;i<arms.length;i++)good[l][i]=bad.reduce((s,q,z)=>s|(!(arms[i].v&q)?1<<z:0),0);
 }
 const seen=new Set();
 for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
   counts.pairs++;const a=arms[i],b=arms[j],pos=a.sign|b.sign;
   if(pos===a.sign||pos===b.sign){counts.comparable++;continue;}
   let supp=already;for(let s=pos&~already;s;s&=s-1){const z=31-Math.clz32(s&-s);if(good[z][i]&good[z][j])supp|=1<<z;}
   const n=pc[supp];counts.support[n]=(counts.support[n]||0)+1;
   if(n<5)continue;const u=a.v|b.v;if(w.includes(u))continue;
   const key=u.toString(16)+'/'+[a.v,b.v].map(s=>s.toString(16)).sort().join('/');
   if(seen.has(key))continue;seen.add(key);
   counts.pass5++;if(n>=6)counts.pass6++;
   keep.push([k,a.p,a.j,b.p,b.j,supp]);
 }
}
counts.ms=Date.now()-start;fs.writeFileSync(path.join(__dirname,'bounded-three-screen-'+from+'-'+end+'.json'),JSON.stringify({counts,keep})+'\n');console.log(counts);
