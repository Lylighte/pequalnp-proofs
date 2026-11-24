"use strict";
const fs=require("node:fs"),path=require("node:path");
const w=Array.from({length:32768},(_,i)=>i.toString(2).replace(/0/g,"").length);
const nrows=Number(process.argv[2]||12);const E=[];for(let i=0;i<6;i++)for(let j=0;j<i;j++)E.push((1<<i)|(1<<j));
const T=Array.from({length:64},(_,s)=>s).filter(s=>w[s]===3);
const si=Array.from({length:64},(_,s)=>E.reduce((m,e,i)=>m|(((e&s)===e)?1<<i:0),0));
const fcost=n=>(6-n)*(5-n)/2,perms=[];
function perm(p){if(p.length===6){perms.push(p);return;}for(let i=0;i<6;i++)if(!p.includes(i))perm([...p,i]);}
perm([]);
const emaps=perms.map(p=>E.map(e=>E.indexOf(p.reduce((m,v,i)=>m|(((1<<i)&e)?1<<v:0),0))));
const seen=new Set(),recs=[];
for(let graph=0;graph<32768;graph++){
    const k=w[graph];if(k<4||k>nrows||seen.has(graph))continue;
    const orbit=new Set(emaps.map(map=>map.reduce((m,v,i)=>m|((graph&(1<<i))?1<<v:0),0)));
    for(const e of orbit)seen.add(e);
    const sk=[0,...E.map((e,i)=>(graph&(1<<i))?1<<i:0).filter(Boolean)];
    const choices=sk.map(mark=>{
        const c=Array.from({length:64},(_,s)=>s).filter(s=>(si[s]&graph)===mark&&w[s]>=2);
        return c.filter(s=>!c.some(a=>a!==s&&(a&s)===s));
    });
    const low=choices.map(c=>c.length?Math.min(...c.map(s=>fcost(w[s]))):99);
    const lower=low[0]*(nrows-k)+low.slice(1).reduce((a,b)=>a+b,0);
    let yes=false;
    if(lower<=30){
        const req=[...choices.slice(1),...Array.from({length:nrows-k},()=>choices[0])].sort((a,b)=>a.length-b.length);
        const budgets=E.map(()=>2).concat(T.map(()=>1)),features=Array.from({length:64},(_,s)=>[...E,...T].map((p,i)=>(p&s)?-1:i).filter(i=>i>=0));
        function search(j){
            if(j===nrows)return true;
            for(const s of req[j]){
                const costs=features[s];if(costs.some(i=>!budgets[i]))continue;
                costs.forEach(i=>budgets[i]--);
                if(search(j+1))return true;
                costs.forEach(i=>budgets[i]++);
            }
            return false;
        }
        yes=search(0);
    }
    recs.push({graph,k,orbit:orbit.size,lower,yes});
}
const sums={};
for(const r of recs){const v=sums[r.k]??={tested:0,passedCost:0,passedSeparate:0,least:99};v.tested+=r.orbit;if(r.lower<=30)v.passedCost+=r.orbit;if(r.yes)v.passedSeparate+=r.orbit;v.least=Math.min(v.least,r.lower);}
fs.writeFileSync(path.join(__dirname,"small-core","pair-edges-"+nrows+".json"),JSON.stringify({sums,recs},null,2)+"\n");
console.log(JSON.stringify(sums));
