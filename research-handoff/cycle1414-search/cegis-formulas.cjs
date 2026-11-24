const {build,inputs,target,mask,rows,goal}=require('./formula.cjs'),fs=require('node:fs'),path=require('node:path');
const {check}=require('./verify.cjs'),assert=require('node:assert/strict');
const dp=build(true,10),{d,at}=dp,memo=new Map();
function items(t){
 if(memo.has(t))return memo.get(t);
 const n=d[t],ans=[];
 if(n===0)return [inputs.indexOf(t)];
 if(d[t^mask]===n-1)for(const a of items(t^mask))ans.push(['!',a]);
 for(let i=0;i<=(n-1)/2;i++){
   const j=n-1-i,a=at[i],b=at[j];
   for(let k=0;k<a.length;k++)for(let h=i===j?k:0;h<b.length;h++){
     const x=a[k],y=b[h];
     for(const op of ['&','|']){
        if((op==='&'?(x&y):(x|y))!==t)continue;
        for(const l of items(x))for(const r of items(y))ans.push([op,l,r]);
     }
   }
 }
 memo.set(t,ans);return ans;
}
function emit(f,g){
 if(typeof f==='number')return f;
 const wires=f.slice(1).map(x=>emit(x,g));g.push([f[0],...wires]);return 6+g.length;
}
const forms=items(target),fail=new Uint32Array(128),hist={},good=[];
for(const f of forms){
 const g=[];emit(f,g);
 const verify=m=>{
   const w=Array.from({length:7},(_,i)=>!!(m&(1<<i)));
   for(const [o,l,r] of g) w.push(o==='!'?!w[l]:o==='&'?(w[l]&&w[r]):(w[l]||w[r]));
   return w.at(-1)===goal(m);
 };
 let correct=true;for(let m=0;m<128;m++)if(!verify(m)){fail[m]++;correct=false;}
 if(correct){const ck=check(g);assert(ck.correct);const n=ck.tight.filter(Boolean).length;hist[n]=(hist[n]||0)+1;good.push(g);}
}
const worst=Array.from(fail,(n,m)=>[m,n]).filter(x=>x[1]).sort((a,b)=>b[1]-a[1]).slice(0,8);
console.log({rows,min:d[target],forms:forms.length,real:good.length,hist,worst});
fs.writeFileSync(path.join(__dirname,'cegis-'+rows.length+'-'+rows.slice(14).join('-')+'.json'),JSON.stringify({rows,min:d[target],forms:forms.length,real:good.length,hist,worst})+'\n');
