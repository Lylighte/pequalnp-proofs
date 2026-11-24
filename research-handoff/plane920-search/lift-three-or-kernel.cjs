const fs=require('node:fs'),path=require('node:path');
const {rawProds}=require('./bounded-three-or.cjs');
const {table,pc,pm,loc,lines,raw,univ}=require('./three-or-five-lines.cjs'),{pricedTables}=require('./paid-or-arms.cjs');
const cores=require('./three-line-five-cores.json'),rawSet=new Set(raw);
const basics=lines.map(L=>{const v=[];for(let s=L;s;s=(s-1)&L)if(pc[s]===2||pc[s]===3)v.push([pc[s],table([s])]);return v;});
const familySets=[5,6].map(k=>Array.from({length:8192},(_,i)=>i).filter(m=>pc[m]===k&&(m&7)===7));
const stats={seed:0,original:0,screened5:0,screened6:0,priced5:0,priced6:0,live:[]};
function liftOptions(after,prev,wanted){
 const prods=[[univ,univ,0]];for(let i=0;i<prev.length;i++)for(const [x,y,s] of [...prods])prods.push([x&prev[i],y&after[i],s|1<<i]);
 const vals=new Map();for(const r of rawProds)for(const [x,y,j] of prods){
  if(!r.p&&!j)continue;if((r.v&y)!==wanted)continue;const v=r.v&x;
  if(!vals.has(v))vals.set(v,{v,p:r.p,j});
 }return [...vals.values()];
}
for(let ci=0;ci<cores.length;ci++){
 const core=cores[ci].row,ref=[core.firstOr.map(p=>table([p])),[table(core.a),table(core.b)]];
 for(const H of rawProds)if(pc[H.p]===2&&!(H.s&7))for(const B of rawProds){
  if(!B.p||!(B.s&~H.s)||!(H.s&~B.s))continue;stats.seed++;
  const x=H.v|B.v,goods=ref[0].map(t=>liftOptions([B.v],[x],t));
  for(const u of goods[0])for(const v of goods[1]){
   const y=u.v|v.v;if(y===x||y===u.v||y===v.v)continue;
   const after=[B.v,ref[0][0]|ref[0][1]],prev=[x,y],next=ref[1].map(t=>liftOptions(after,prev,t));
   for(const s of next[0])for(const t of next[1]){
    const z=s.v|t.v;if(z===s.v||z===t.v||prev.includes(z))continue;stats.original++;
    const flags=[x,y,z],pairs=[[H.v,B.v],[u.v,v.v],[s.v,t.v]],paid=new Set(),known=new Set(raw),cuts=[];
    let old=0;for(const [a,b] of pairs){const p=pm(a),q=pm(b);cuts.push(p&~q,q&~p);if(!known.has(a))paid.add(a);if(!known.has(b))paid.add(b);known.add(flags[old++]);}
    const f=[...paid],alive=f.map(pm),strong=loc.map(at=>flags.reduce((w,g)=>(at&g)?w&g:w,univ));
    let zero=0,one=0;const byForced=f.map(()=>0);
    for(let i=0;i<13;i++){
      const w=strong[i];for(const [n,p] of basics[i])if((p&w)===loc[i]){if(n===2)zero|=1<<i;one|=1<<i;}
      if(!(one&1<<i))continue;
      for(let j=0;j<f.length;j++)if(alive[j]&1<<i){
        if((zero&1<<i)||raw.some(p=>(p&loc[i])&&(p&f[j]&w)===loc[i]))byForced[j]|=1<<i;
      }
    }
    for(let k=5;k<=6;k++){
     if(pc[one]<k)continue;stats['screened'+k]++;
     for(const fam of familySets[k-5]){
      if((fam&H.s)!==H.s||(fam&one)!==fam||cuts.some(c=>!(c&fam)))continue;
      let priv=0,bad=false;for(let j=0;j<f.length;j++){const m=alive[j]&fam;if(pc[m]!==1)continue;
        if((priv&m)||!(byForced[j]&m)){bad=true;break;}priv|=m;}
      if(bad)continue;stats['priced'+k]++;
      const r=pricedTables(flags,f,k,2*k-2,fam,1,cuts);
      if(r.found)stats.live.push({k,ci,H:H.p,B:B.p,first:[u,v].map(({p,j})=>[p,j]),second:[s,t].map(({p,j})=>[p,j]),fam,r});
     }
    }
   }
  }
 }
}
fs.writeFileSync(path.join(__dirname,'lift-three-or-kernel.json'),JSON.stringify(stats)+'\n');
console.log({...stats,live:stats.live.length});
