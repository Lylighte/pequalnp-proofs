"use strict";
const fs = require("node:fs");
const path = require("node:path");
const N = 8192, full = N-1, inf = 70;
const lines = Array.from({length:13}, (_,i)=>[0,1,3,9].reduce((m,x)=>m|1<<((x+i)%13),0));
const pc = new Uint8Array(N);
for (let u=1;u<N;u++) pc[u]=1+pc[u&(u-1)];
const dp = [new Uint8Array(N), new Uint8Array(N)];
const fullAndCuts = {};
function side(normal, groups, own, e) {
    const fixed = dp[e][own], cap = pc[own]-1;
    const ordinary = Math.max(fixed, normal);
    let best = ordinary<=cap ? ordinary : inf;
    for (const costs of groups.values()) {
        costs.sort((x,y)=>y-x);
        let saved=0;
        for(let j=0;j<costs.length;j++) {
            saved+=costs[j];
            const lower=Math.max(fixed,normal-saved);
            // Waving j+1 sections requires j ORs in the common driver.
            if (lower<=cap && lower+j<=cap+e && lower<best) best=lower;
        }
    }
    return best;
}
for(let u=1;u<N;u++) {
    if(pc[u]<2) continue;
    let best=[inf,inf];
    for(let a=(u-1)&u; a; a=(a-1)&u) {
        const b=u^a;
        if(a>b)continue;
        if(u!==full && dp[0][a]+dp[0][b]>=best[0] &&
           Math.min(dp[1][a]+dp[0][b],dp[0][a]+dp[1][b])>=best[1])continue;
        let na=0,nb=0;
        const groupsA=new Map(),groupsB=new Map();
        for(const l of lines) {
            const x=l&a, y=l&b;
            if(!x||!y)continue;
            const cx=pc[x]-1,cy=pc[y]-1;
            na+=cx; nb+=cy;
            if(cx) {
                if(!groupsA.has(y))groupsA.set(y,[]);
                groupsA.get(y).push(cx);
            }
            if(cy) {
                if(!groupsB.has(x))groupsB.set(x,[]);
                groupsB.get(x).push(cy);
            }
        }
        const aa=[side(na,groupsA,a,0),side(na,groupsA,a,1)];
        const bb=[side(nb,groupsB,b,0),side(nb,groupsB,b,1)];
        for(const [ea,eb] of [[0,0],[0,1],[1,0]]) {
            const e=ea+eb;
            const ra=Math.max(na,dp[ea][a]), rb=Math.max(nb,dp[eb][b]);
            if(ra<=pc[a]-1&&rb<=pc[b]-1)best[e]=Math.min(best[e],ra+rb);
            best[e]=Math.min(best[e],1+aa[ea]+bb[eb]);
            if(u===full && e===1 && 1+aa[ea]+bb[eb]<=8) {
                const sizes=[pc[a],pc[b]].sort((x,y)=>x-y);
                const key=sizes.join("+")+"/extra"+(ea?pc[a]:pc[b]);
                fullAndCuts[key]=(fullAndCuts[key]??0)+1;
            }
        }
        best[1]=Math.min(best[1],best[0]);
    }
    const seven=process.argv.includes("--seven")&&pc[u]===7?3:0;
    dp[0][u]=Math.max(best[0],seven); dp[1][u]=Math.max(best[1],seven);
}
const hist=[{},{}];
for(let e=0;e<2;e++)for(let u=1;u<N;u++){
    const row=hist[e][pc[u]]??={};
    row[dp[e][u]]=(row[dp[e][u]]??0)+1;
}
const result={full:dp.map(d=>d[full]),hist,fullAndCuts,
    assumptions:"hidden forest or one same-component OR; opposite-side exception overlap relaxed"};
fs.writeFileSync(path.join(__dirname,process.argv.includes("--seven")?"cut-budget-seven.json":"cut-budget.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify(result.full));
