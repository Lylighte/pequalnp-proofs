const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {orbits,next,table,mult,raw,loc,lines,univ,pm,pc,perm,rel}=require('./three-or-five-lines.cjs');
const {inspect}=require('./private-independent.cjs');
const initial=[1,2],st=perm.filter(p=>rel(initial,p)==='1,2'),seconds=orbits(next([initial]),st);
const residual=[],control={n:0},stats={},start=Date.now();let roots=0,pairs=0,dominance=0,checked=0,fullCandidates=0;
for(const s of seconds)for(const q of orbits(next([initial,s.t]),s.stab)){
 const gates=[initial,s.t,q.t],w=gates.map(table),prods=[{t:[0],w:univ}];
 for(let i=0;i<3;i++)for(const z of [...prods])prods.push({t:mult(z.t,gates[i]),w:z.w&w[i]});
 const map=new Map();
 for(let r=-1;r<13;r++)for(let j=0;j<prods.length;j++){
   if(r<0&&!j)continue;const p=prods[j],t=r<0?p.t:mult(p.t,[1<<r]);if(pc[t.reduce((v,m)=>v&m,8191)]>1)continue;
   const v=p.w&(r<0?univ:raw[r]);map.set(t.join(','),{v,pos:pm(v),choice:[r,j],good:new Uint8Array(13)});
 }
 const arms=[...map.values()];let base=0;
 for(let i=0;i<13;i++){
   const pts=raw.map((_,k)=>k).filter(k=>lines[i]&1<<k),z=w.reduce((v,t)=>v&((t&loc[i])?t:univ),univ);
   const bad=[];for(let a=0;a<4;a++)for(let b=0;b<a;b++)bad.push((z&raw[pts[a]]&raw[pts[b]])^loc[i]);
   if(bad.includes(0n))base|=1<<i;
   for(const v of arms)for(let k=0;k<bad.length;k++)if(!(bad[k]&v.v))v.good[i]|=1<<k;
 }
 for(let a=0;a<arms.length;a++)for(let b=0;b<a;b++){
   pairs++;const x=arms[a],y=arms[b],v=x.pos|y.pos;if(v===x.pos||v===y.pos){dominance++;continue;}
   let covered=base;
   for(let i=0;i<13;i++)if((v&1<<i)&&(x.good[i]&y.good[i]))covered|=1<<i;
   const n=pc[covered];stats[n]=(stats[n]||0)+1;
   if(n>=4||((a*113+b*127+roots)%997===0)){
     const cost=inspect([...w,x.v|y.v],100).costs,real=cost.reduce((m,c,i)=>m|(!c?1<<i:0),0);
     assert.equal(real&~covered,0);control.n++;
     if(n>=4){fullCandidates++;if(pc[real]>=4)residual.push({gates,a:x.choice,b:y.choice,real});}
   }
 }
 roots++;
}
const summary={roots,pairs,dominance,stats,fullCandidates,fullChecks:control.n,exactResidual:residual.length,ms:Date.now()-start};
fs.writeFileSync(path.join(__dirname,'four-or-free-intersection.json'),JSON.stringify({summary,residual})+'\n');console.log(summary);
