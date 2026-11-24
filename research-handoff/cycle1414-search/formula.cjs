const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const edge=Array.from({length:7},(_,i)=>(1<<i)|(1<<((i+1)%7)));
const goal=m=>edge.some(e=>(e&m)===e);
const neg=Array.from({length:128},(_,i)=>i).filter(m=>!goal(m)&&Array.from({length:7},(_,i)=>1<<i).every(v=>(v&m)||goal(v|m)));
const extra=(process.env.CYCLE1414_ROWS||'').split(',').filter(Boolean).map(Number);
const rows=[...new Set([...edge,...neg,...extra])];
const sig=f=>rows.reduce((n,r,i)=>n+(f(r)?1<<i:0),0);
const inputs=Array.from({length:7},(_,i)=>sig(r=>r&(1<<i))),target=sig(goal),mask=(1<<rows.length)-1;
function build(not,limit,seeds=inputs){
 const d=new Int8Array(mask+1).fill(99),at=Array.from({length:limit+1},()=>[]);
 const add=(v,t)=>{if(d[v]>t){d[v]=t;at[t].push(v);}};
 for(const val of seeds)add(val,0);
 for(let s=1;s<=limit;s++){
   if(not)for(const u of at[s-1])add(u^mask,s);
   for(let i=0;i<=(s-1)/2;i++){
     const j=s-1-i,aa=at[i],bb=at[j];
     for(let k=0;k<aa.length;k++)for(let n=(i===j?k:0);n<bb.length;n++){
       const a=aa[k],b=bb[n];add(a|b,s);add(a&b,s);
     }
   }
 }
 return {d,at};
}
function minCount(not,dp){
 const {d,at}=dp,memo=new Map();
 function count(t){
   if(memo.has(t))return memo.get(t);
   const s=d[t];if(!s)return 1n;
   let ans=0n;
   if(not&&d[t^mask]===s-1)ans+=count(t^mask);
   for(let i=0;i<=(s-1)/2;i++){
     const j=s-1-i,aa=at[i],bb=at[j];
     for(let k=0;k<aa.length;k++)for(let n=(i===j?k:0);n<bb.length;n++){
       const a=aa[k],b=bb[n];if((a&b)!==t&&(a|b)!==t)continue;
       const x=count(a),y=count(b);ans+=a===b?x*(x+1n)/2n:x*y;
     }
   }
   memo.set(t,ans);return ans;
 }
 return count(target);
}
if(require.main===module){
  const report={rows,inputs,target,tests:[]};
  for(const not of [false,true]){
    const dp=build(not,10);
    report.tests.push({not,targetMin:dp.d[target],states:dp.at.map(x=>x.length),minimumFormulaCount:minCount(not,dp).toString()});
  }
  fs.writeFileSync(path.join(__dirname,'formula-boundary.json'),JSON.stringify(report,null,2)+'\n');console.log(report);
}
module.exports={build,rows,inputs,target,mask,goal,edge,neg};
