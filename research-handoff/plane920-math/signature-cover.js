"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const {lines,weight}=require("./plane-orbits.js"),{checkProof}=require("../plane920-search/stream-rup.cjs");
const n=Number(process.argv[2]??6),k=Number(process.argv[3]??250000),rank=process.argv.includes("--rank"),pinned=rank||process.argv.includes("--first");
const lowArg=process.argv.find(a=>a.startsWith("low=")),low=lowArg?Number(lowArg.slice(4)):0;
const pinArg=process.argv.find(a=>a.startsWith("high=")),pins=pinArg?pinArg.slice(5).split(",").map(Number).sort((a,b)=>a-b):null,free=process.argv.includes("--free-or");
let nv=0;const cl=[],v=()=>++nv,helper=Array.from({length:n},()=>lines.map(v));
function clause(...a){cl.push(a);}
// Sort the unlabeled helper signatures to reduce permutations. Leave slot 0 fixed if it has special semantics.
for(let g=rank?4:pinned?2:1;g<n;g++){
    if(low&&g===low)continue;
    let eq=0;
    for(let i=12;i>=0;i--){
        const a=helper[g-1][i],b=helper[g][i],nex=v(),start=eq?[-eq]:[];
        clause(...start,-a,b);clause(...start,-a,-b,nex);clause(...start,a,b,nex);eq=nex;
    }
}
if(pins)for(let j=0;j<pins.length;j++)for(let i=0;i<13;i++)clause(((pins[j]>>i)&1?1:-1)*helper[low+j][i]);
const rawUsed=Array.from({length:n},()=>lines.map(v));
if(rank){
    for(let j=0;j<n;j++)for(let i=0;i<13;i++)
        clause(...helper[j].filter((_,r)=>i!==r));
    for(let j=1;j<Math.max(3,low);j++)for(let i=0;i<13;i++)for(let q=0;q<i;q++)clause(-rawUsed[j][i],-rawUsed[j][q]);
    if(low)for(let L=0;L<13;L++)for(let j=0;j<low;j++)clause(...helper.slice(0,low).filter((_,i)=>i!==j).map(t=>t[L]));
    const menus=[lines.map(v),lines.map(v)],cover=lines.map(v),inter=lines.map(v),anyInter=v();
    for(let i=0;i<13;i++){const a=menus[0][i],b=menus[1][i];clause(-a,cover[i]);clause(-b,cover[i]);clause(-a,-b,inter[i]);clause(-inter[i],anyInter);}
    for(let m=0;m<8192;m++)if(!free&&(weight[m]===10||weight[m]===9)){
        const lits=cover.filter((_,i)=>m&(1<<i)).map(q=>-q);
        if(weight[m]===9)lits.push(-anyInter);clause(...lits);
    }
    for(let i=0;i<13;i++){
        const hits=menus.map(menu=>{
            const a=v(),ls=menu.filter((_,j)=>lines[i]&(1<<j));clause(-a,...ls);
            for(const b of ls)clause(-b,a);return a;
        });
        clause(-helper[0][i],hits[0]);clause(-helper[0][i],hits[1]);clause(helper[0][i],-hits[0],-hits[1]);
    }
}
for(let m=1;m<8192;m++)if(weight[m]===2||weight[m]===3){
    const rows=lines.map((_,i)=>i).filter(i=>m&(1<<i));
    const need=weight[m]===2?4:5;
    for(let subset=0;subset<(1<<n);subset++)if(weight[subset]===n-need+1)
        clause(...helper.flatMap((s,i)=>subset&(1<<i)?rows.map(t=>s[t]):[]));
}
for(let L=0;L<13;L++){
    const opts=[];
    for(let i=0;i<n;i++){
        if(!pinned||i!==0)for(let p=0;p<13;p++)if(lines[L]&(1<<p)){
            const h=v();opts.push(h);clause(-h,helper[i][L]);clause(-h,rawUsed[i][L]);
            for(let t=0;t<13;t++)if(t!==L&&lines[t]&(1<<p))clause(-h,-helper[i][t]);
        }
        for(let j=0;j<i;j++){
            if(rank&&i===1&&j===0)continue;
            const h=v();opts.push(h);clause(-h,helper[i][L]);clause(-h,helper[j][L]);
            for(let t=0;t<13;t++)if(t!==L)clause(-h,-helper[i][t],-helper[j][t]);
        }
    }
    clause(...opts);
}
const s="p cnf "+nv+" "+cl.length+"\n"+cl.map(c=>c.join(" ")+" 0").join("\n")+"\n",base=path.join(__dirname,"small-core","signature-"+n+(rank?"-rank":pinned?"-first":"")+(low?"-low"+low:"")+(free?"-free":"")+(pins?"-"+pins.join("-"):""));
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
fs.writeFileSync(base+".cnf",s);
(async()=>{
    const proc=cp.spawnSync(bin,["-q","--plain","--lrat","--no-binary","-c",String(k),base+".cnf",base+".lrat"],{encoding:"utf8",timeout:55000,windowsHide:true});
    const verdict=proc.status===20?"UNSAT":proc.status===10?"SAT":"UNKNOWN";
    const r={n,pinned,k,verdict};
    if(verdict==="UNSAT")r.check=await checkProof(s,base+".lrat");
    if(verdict==="SAT"){
        const yes=new Set(proc.stdout.split(/\r?\n/).filter(l=>l.startsWith("v ")).flatMap(l=>l.slice(2).split(/\s+/).map(Number)).filter(i=>i>0));
        r.signatures=helper.map(w=>w.reduce((m,x,i)=>m|(yes.has(x)?1<<i:0),0));
    }
    fs.writeFileSync(base+".json",JSON.stringify(r,null,2)+"\n");console.log(JSON.stringify(r));
})().catch(e=>{console.error(e);process.exitCode=1;});
