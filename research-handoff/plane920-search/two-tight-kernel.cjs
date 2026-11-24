const fs=require('node:fs'),path=require('node:path');
const {roots,terms}=require('./bounded-three-or.cjs'),{table,pm,join,pc,raw,loc,lines,univ}=require('./three-or-five-lines.cjs'),{priced}=require('./paid-or-arms.cjs');
const secondMaps=new Map();
function decomps(root){
 const [a,b]=root,key=a.toString();
 if(!secondMaps.has(key)){
  const bank=new Map(),opts=terms([a]);
  for(let i=0;i<opts.length;i++)for(let j=0;j<i;j++){
    const x=opts[i],y=opts[j];if(!(x.sign&~y.sign)||!(y.sign&~x.sign))continue;
    const t=join(x.t,y.t),name=t.toString();if(name===key)continue;
    if(!bank.has(name))bank.set(name,[]);bank.get(name).push([x.t,y.t]);
  }secondMaps.set(key,bank);
 }return secondMaps.get(key).get(b.toString());
}
function paidFor(root,ps){
 const free=new Set(raw),paid=new Map(),cuts=[];
 ps.forEach((pair,j)=>{const [a,b]=pair.map(t=>pm(table(t)));cuts.push(a&~b,b&~a);
  for(const t of pair){const w=table(t);if(!free.has(w))paid.set(w,t);}free.add(table(root[j]));
 });
 return {paid:[...paid.values()],cuts};
}
function screen(root){
 const flags=root.map(table);
 return lines.reduce((mask,L,i)=>{
  const w=flags.reduce((s,g)=>(g&loc[i])?s&g:s,univ);
  for(let z=L;z;z=(z-1)&L)if(pc[z]===3&&(table([z])&w)===loc[i])return mask|1<<i;
  return mask;
 },0);
}
if(require.main===module){
 const k=Number(process.argv[2]||4),end=Math.min(roots.length,Number(process.argv[3]||roots.length)),stats={k,end,okRoots:0,payTests:0,live:[]};
 for(let j=0;j<end;j++){
  const gs=roots[j],ok=screen(gs);if(pc[ok]<k)continue;stats.okRoots++;
  for(const [A,B] of decomps(gs)){
   const ps=[gs[0].map(x=>[x]),[A,B]],{paid,cuts}=paidFor(gs,ps);
   if(cuts.some(m=>!(m&ok)))continue;stats.payTests++;
   const r=priced(gs,paid,k,2*k-1,0,1,cuts);
   if(r.found)stats.live.push({j,ps,r});
  }
 }
 fs.writeFileSync(path.join(__dirname,'two-tight-kernel-'+k+'-'+end+'.json'),JSON.stringify(stats)+'\n');
 console.log({...stats,live:stats.live.length});
}
module.exports={decomps,paidFor,screen};
