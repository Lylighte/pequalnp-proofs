const fs=require('node:fs'),path=require('node:path');
const {families,prefixes}=require('./five-or-six-targets.cjs');
const {lines,loc,raw,univ,table,pc}=require('./three-or-five-lines.cjs');
const {inspect}=require('./private-independent.cjs');
const seven=process.argv.includes('--seven'),kLines=seven?7:6,maxCost=seven?3:2;
const lim=Number(process.argv[2]||1000000),start=Date.now(),out=[];
const only=Number((process.argv.find(x=>x.startsWith('--one='))||'--one=0').slice(6));
for(const {m,gp} of families){if(only&&m!==only)continue;
 const sel=lines.map((L,i)=>({L,i})).filter(x=>m&1<<x.i),M=(1<<kLines)-1,at=sel.map(x=>loc[x.i]);
 const pos=w=>at.reduce((v,b,i)=>v|((w&b)?1<<i:0),0);
 const basic=sel.map(({L})=>{const masks=[];for(let sub=L;sub;sub=(sub-1)&L)if(pc[sub]===2||pc[sub]===3)masks.push({sub,n:pc[sub],v:table([sub])});return masks;});
 function arms(prev){
  const parts=[univ];for(const t of prev)for(const x of [...parts])parts.push(x&t);
  const store=new Map();for(let p=-1;p<13;p++)for(let j=0;j<parts.length;j++){
   if(p<0&&!j)continue;const v=parts[j]&(p<0?univ:raw[p]);if(store.has(v))continue;
   const s=pos(v);if(pc[s]>=2&&(!process.argv.includes('--pay3')||pc[s]>=3||prev.includes(v)||raw.includes(v)))store.set(v,{v,s,p,j});
  }return [...store.values()];
 }
 const stats={m,three:0,four:0,preFour:0,coarseLate:0,exactLate:0,inspectOK:0,sample:[]};
 prefixes(m,gp,3,(terms,group)=>{
  if(stats.three++>=lim)return;
  const prev=terms.map(table),pr=sel.map(({i})=>prev.reduce((v,o)=>(o&loc[i])?v&o:v,univ));
  const fourth=arms(prev),seen4=new Set();
  for(let ai=0;ai<fourth.length;ai++)for(let bi=0;bi<ai;bi++){
   const a=fourth[ai],b=fourth[bi];if(pc[a.s&~b.s]<2||pc[b.s&~a.s]<2)continue;
   const q=a.v|b.v;if(seen4.has(q)||prev.includes(q))continue;seen4.add(q);stats.four++;
   let old0=0,old1=0;
   const step0=new Uint8Array(14),step1=new Uint8Array(14),bad=[];
   for(let i=0;i<kLines;i++){
    const base=pr[i]&((q&at[i])?q:univ);let two=0,three=0;
    bad[i]=basic[i].map(z=>{const v=(z.v&base)^at[i];if(!v){if(z.n===2)two|=z.sub;else three|=z.sub;}return v;});
    if(two)old0|=1<<i;if(three)old1|=1<<i;
    for(let p=-1;p<13;p++){
     if(two||(p>=0&&(three&1<<p)))step0[p+1]|=1<<i;
     if(three||(p>=0&&(sel[i].L&1<<p)))step1[p+1]|=1<<i;
    }
   }
   if(pc[old1]<4)continue;stats.preFour++;
   const flags=[...prev,q],fifth=arms(flags),seen5=new Set();
   for(const x of fifth){
     x.z=(M^x.s)|step0[x.p+1];x.o=(M^x.s)|step1[x.p+1];
   }
   for(let i=0;i<fifth.length;i++)for(let j=0;j<i;j++){
    const x=fifth[i],y=fifth[j],s=x.s|y.s;
    if(pc[x.s&~y.s]<2||pc[y.s&~x.s]<2)continue;
    const rz=(s&x.z&y.z)|(old0&~s),ro=(s&x.o&y.o)|(old1&~s);
    if(pc[rz]+pc[ro]<2*kLines-maxCost)continue;stats.coarseLate++;
    const u=x.v|y.v;if(seen5.has(u))continue;seen5.add(u);
    let price=0;for(let k=0;k<kLines&&price<=maxCost;k++){
     if(!(s&1<<k)){price+=((old0&1<<k)?0:(old1&1<<k)?1:2);continue;}
     let c=2;for(let el=0;el<bad[k].length;el++)if(!(bad[k][el]&u)){c=Math.min(c,basic[k][el].n-2);if(!c)break;}
     price+=c;
    }
    if(price>maxCost)continue;stats.exactLate++;
    const exact=inspect([...flags,u],100).costs;
    if(sel.reduce((n,z)=>n+exact[z.i],0)>maxCost)continue;
    stats.inspectOK++;if(stats.sample.length<4||process.argv.includes('--all'))stats.sample.push({terms,ai,bi,i,j,exact,pairs:[[a.p,a.j],[b.p,b.j],[x.p,x.j],[y.p,y.j]]});
   }
  }
 });
 out.push(stats);console.log({...stats,sample:stats.sample.length});
}
fs.writeFileSync(path.join(__dirname,(seven?'seven-target-last-or-':'six-target-last-or-')+lim+(only?'-'+only:'')+(process.argv.includes('--pay3')?'-pay3':'')+'.json'),JSON.stringify({out,ms:Date.now()-start})+'\n');
