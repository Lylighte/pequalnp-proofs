const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {runPrefix}=require('./surplus-fifth.cjs'),{lines}=require('./branch-game.json'),forest=require('../plane920-core/or-forest-five.json');
const domain=Array.from({length:8192},(_,i)=>i).filter(m=>m.toString(2).replaceAll('0','').length<=4);
const all=(1n<<BigInt(domain.length))-1n;
const raw=Array.from({length:13},(_,p)=>domain.reduce((s,m,j)=>s|((m&1<<p)?1n<<BigInt(j):0n),0n));
const target=lines.map(m=>1n<<BigInt(domain.indexOf(m))),pts=lines.map(m=>raw.map((_,i)=>i).filter(i=>m&1<<i));
const pairs=lines.map(l=>lines.map(m=>31-Math.clz32(l&m)));
function inspect(gates,cap){
 const flags=target.map(t=>gates.reduce((m,v,j)=>m|((t&v)?1<<j:0),0));
 const prod=[all];for(const g of gates){const n=prod.length;for(let i=0;i<n;i++)prod.push(prod[i]&g);}
 const costs=[];
 let total=0;
 for(let t=0;t<13;t++){
   const leaves=new Set(pts[t].map(p=>raw[p]));
   for(const g of gates)if(g&target[t])leaves.add(g);
   for(let j=0;j<13;j++)if(j!==t)leaves.add(raw[pairs[t][j]]&prod[flags[t]&flags[j]]);
   const bad=[...leaves].map(v=>v^target[t]);
   const minimal=bad.filter((v,i)=>!bad.some((u,j)=>i!==j&&(u&v)===u));
   let cost=2;
   for(let i=0;i<minimal.length;i++)for(let j=0;j<=i;j++){
     const pair=minimal[i]&minimal[j];
     if(!pair){cost=0;break;}
     if(cost>1)for(let k=0;k<j;k++)if(!(minimal[k]&pair)){cost=1;break;}
   }
   costs.push(cost);total+=cost;
   if(total>cap)break;
 }
 return {total,costs};
}
if(require.main===module){
 const t=Date.now(),totals={},seen=Array(14).fill(0),survivors=[],full=process.argv.includes('--exhaust'),limit=Number(process.argv.find(v=>/^\d+$/.test(v))||238);
 let num=0;
 for(const f of forest.prefixes.slice(0,limit)){
   runPrefix(f,({orbit,number,ors,e})=>{
     const {total,costs}=inspect([...ors.map(v=>v.w),e.w],full?100:8);
     totals[total]=(totals[total]||0)+1;seen[costs.length]++;
     if(total<=8)survivors.push({orbit,number,total,costs});num++;
   });
 }
 const summary={prefixes:limit,num,full,totals,seen,survivors,ms:Date.now()-t,rows:domain.length};
 if(limit===238)assert.equal(num,167922);
 fs.writeFileSync(path.join(__dirname,'private-independent-'+(full?'full':'fast')+'.json'),JSON.stringify(summary)+'\n');console.log({num,totals,rows:domain.length,survivors:survivors.length,ms:summary.ms});
}
module.exports={inspect};
