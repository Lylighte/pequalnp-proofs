const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {build,inputs,target}=require('./formula.cjs'),{check}=require('./verify.cjs');
const {d,at}=build(false,10),memo=new Map;
function dec(t){
 if(memo.has(t))return memo.get(t);
 const s=d[t],o=[];
 if(!s)return [inputs.indexOf(t)];
 for(let i=0;i<=(s-1)/2;i++){
   const j=s-1-i,aa=at[i],bb=at[j];
   for(let k=0;k<aa.length;k++)for(let n=i===j?k:0;n<bb.length;n++){
     const a=aa[k],b=bb[n];if((a&b)!==t&&(a|b)!==t)continue;
     const op=(a&b)===t?'&':'|';
     for(const l of dec(a))for(const r of dec(b))o.push([op,l,r]);
   }
 }
 memo.set(t,o);return o;
}
function circuit(form){
 const g=[];
 function f(x){if(typeof x==='number')return x;const [op,l,r]=x,a=f(l),b=f(r);g.push([op,a,b]);return 6+g.length;}
 f(form);return g;
}
const forms=dec(target),freq={},records=[],best={t:99};
for(const f of forms){
 const gates=circuit(f);assert.equal(gates.length,10);
 const r=check(gates);assert(r.correct);
 const t=r.tight.filter(Boolean).length;
 freq[t]=(freq[t]||0)+1;records.push({gates,elim:r.elim.map(x=>x.length)});
 if(t<best.t)Object.assign(best,{t,gates,elim:r.elim});
}
assert.equal(forms.length,147);
fs.writeFileSync(path.join(__dirname,'monotone-formula-witnesses.json'),JSON.stringify({freq,best,records})+'\n');
console.log({forms:forms.length,freq,best});
