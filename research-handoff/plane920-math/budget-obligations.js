"use strict";
const fs=require("node:fs"),path=require("node:path");
const N=8192,F=N-1,lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,v)=>m|1<<((v+i)%13),0));
const pc=new Uint8Array(N);
for(let u=1;u<N;u++)pc[u]=1+pc[u&(u-1)];
const large=new Uint16Array(N), lb0=new Uint8Array(N), cuts=new Map();
const atLeastThree = new Uint16Array(N);
for(let u=1;u<N;u++) for(let i=0;i<13;i++) if(pc[lines[i]&u]>=2)large[u]|=1<<i;
for(let u=1;u<N;u++) for(let i=0;i<13;i++) if(pc[lines[i]&u]>=3)atLeastThree[u]|=1<<i;
// The independent side-cut minimum by cardinality from merge-all-slices.
const minBySize=[0,0,0,0,0,1,1,3,3,4,5,6,7,8];
for(let u=1;u<N;u++)lb0[u]=minBySize[pc[u]];
const masklb=new Map(),memo=new Map(),keep=new Map();
const colourCache=new Map();
function rainbow(u,mask) {
    const key=u*N+mask;
    if(colourCache.has(key))return colourCache.get(key);
    const targets=[];
    for(let i=0;i<13;i++)if(mask&(1<<i))targets.push(lines[i]&u);
    const pts=Array.from({length:13},(_,x)=>1<<x).filter(x=>x&u).sort(
        (a,b)=>targets.filter(t=>t&b).length-targets.filter(t=>t&a).length);
    const cs=[0,0,0];
    function dfs(i,unassigned,highest) {
        if(i===pts.length)return true;
        const p=pts[i],rem=unassigned^p;
        for(let c=0;c<=Math.min(2,highest+1);c++){
            cs[c]|=p;
            const valid=targets.every(t=>(Number(!(t&cs[0]))+Number(!(t&cs[1]))+
                Number(!(t&cs[2])))<=pc[t&rem]);
            if(valid&&dfs(i+1,rem,Math.max(c,highest))){cs[c]^=p;return true;}
            cs[c]^=p;
        }
        return false;
    }
    const res=dfs(0,u,-1);
    colourCache.set(key,res);return res;
}
function lower(u,h) {
    h&=large[u];const key=u*N+h;
    if(masklb.has(key))return masklb.get(key);
    let total=0;
    for(let s=h;s;s&=s-1) total+=pc[lines[31-Math.clz32(s&-s)]&u]-1;
    // A different target needs a first true AND at a subset of its own row of size at most two.
    // All hard charges have a unique minimum of two or more points on their owner's line.
    const difficult=atLeastThree[u]&~h;
    if(difficult&&!process.argv.includes("--plain"))total+=rainbow(u,difficult)?1:2;
    const ans=Math.max(lb0[u],total);
    masklb.set(key,ans);return ans;
}
function candidates(u) {
    if(cuts.has(u)) return cuts.get(u);
    const out=[];
    for(let a=(u-1)&u;a;a=(a-1)&u){
        const b=u^a;if(a>b)continue;
        const ax=new Map(),by=new Map(),cross=[];
        let crossMask=0;
        for(let i=0;i<13;i++){
            const x=a&lines[i],y=b&lines[i],bit=1<<i;
            if(!x||!y)continue;
            crossMask|=bit;cross.push([bit,x,y]);
            ax.set(x,(ax.get(x)??0)|bit);
            by.set(y,(by.get(y)??0)|bit);
        }
        out.push({a,b,cross,ax,by,crossMask});
    }
    out.sort((i,j)=>Math.min(pc[i.a],pc[i.b])-Math.min(pc[j.a],pc[j.b]));
    cuts.set(u,out);return out;
}
function possible(u,h,budget) {
    h&=large[u];budget=Math.min(budget,pc[u]-1);
    if(lower(u,h)>budget)return false;
    if(pc[u]<=1)return true;
    const key=(u*N+h)*16+budget;
    if(memo.has(key))return memo.get(key);
    function children(a,ha,b,hb,op) {
        const available=budget-op;
        const la=lower(a,ha),lb=lower(b,hb);
        if(la+lb>available)return false;
        for(let ba=la;ba<=Math.min(pc[a]-1,available-lb);ba++) {
            const bb=available-ba;
            if(possible(a,ha,ba)&&possible(b,hb,bb)) {keep.set(key,{u,h,budget,a,b,ha,hb,ba,bb,op});return true;}
        }
        return false;
    }
    for(const {a,b,cross,ax,by,crossMask} of candidates(u)) {
        const hc=h&crossMask;
        if(pc[hc]>1)continue;
        const origA=(h|crossMask)&large[a],origB=(h|crossMask)&large[b];
        if(!hc&&children(a,origA,b,origB,0)){memo.set(key,true);return true;}
        if(!budget)continue;
        const cell=hc?cross.find(([bit])=>bit===hc):null;
        const xs=cell?[cell[1]]:[...ax.keys(),0],ys=cell?[cell[2]]:[...by.keys(),0];
        for(const x of xs)for(const y of ys) {
            const da=(by.get(y)??0)&crossMask&~h,db=(ax.get(x)??0)&crossMask&~h;
            const ha=origA&~da,hb=origB&~db,overlap=da&db&large[a]&large[b];
            // One crossing cell can match both driver minima; only one side can be waived.
            if((!overlap&&children(a,ha,b,hb,1)) ||
               (overlap&&(children(a,ha|overlap,b,hb,1)||children(a,ha,b,hb|overlap,1)))){
                memo.set(key,true);return true;
            }
        }
    }
    memo.set(key,false);return false;
}
const p=0,B=F^1;
const through=lines.reduce((s,l,i)=>s|((l&1)?1<<i:0),0);
function rootCommon(h) {
    const group=through&~h;
    let feasible=0;
    const hist={},examples=[];
    for(const {a,b,cross,ax,by,crossMask} of candidates(B)) {
        const hc=h&crossMask;
        if(pc[hc]>1)continue;
        const hitA=group&lines.reduce((s,l,i)=>s|((l&a)?1<<i:0),0);
        const hitB=group&lines.reduce((s,l,i)=>s|((l&b)?1<<i:0),0);
        const gc=group&crossMask;
        const origA=(h|crossMask)&large[a],origB=(h|crossMask)&large[b];
        const cell=hc?cross.find(([bit])=>bit===hc):null;
        let pass=null;
        function permit(op,ha,hb,kind) {
            if(pass)return;
            const la=lower(a,ha),lb=lower(b,hb);
            for(let ba=la;ba<=Math.min(pc[a]-1,7-op-lb);ba++)
                if(possible(a,ha,ba)&&possible(b,hb,7-op-ba)){
                    pass={a,b,op,ha,hb,ba,bb:7-op-ba,kind};break;
                }
        }
        if(!hc && pc[gc]<=2)permit(0,origA,origB,"OR mixed driver");
        for(const pp of(cell?[cell[1]]:[...ax.keys(),0])){
            if(pass)break;
            for(const qq of(cell?[cell[2]]:[...by.keys(),0])){
                if(pass)break;
                const da=(by.get(qq)??0)&~h,db=(ax.get(pp)??0)&~h;
                const baseA=origA&~da,baseB=origB&~db;
                const both=da&db&large[a]&large[b];
                const opts=both?[[baseA|both,baseB],[baseA,baseB|both]]:[[baseA,baseB]];
                for(const [ha,hb] of opts) {
                    if(group===hitA&&pc[gc]<=2) {
                        const ex=gc&da;
                        for(const w of [0,...Array.from({length:13},(_,i)=>1<<i).filter(bit=>bit&ex)])
                            if(pc[gc&~w]<=1)permit(1,ha|((gc&~w)&large[a]),hb|(gc&large[b]),"A driver");
                    }
                    if(group===hitB&&pc[gc]<=2) {
                        const ex=gc&db;
                        for(const w of [0,...Array.from({length:13},(_,i)=>1<<i).filter(bit=>bit&ex)])
                            if(pc[gc&~w]<=1)permit(1,ha|(gc&large[a]),hb|((gc&~w)&large[b]),"B driver");
                    }
                    if(gc===group&&pc[group]<=2&&(gc&~(da|db))===0&&
                       (pc[group]===1 || ((gc&da)&&(gc&db)&&!((gc&da)===(gc&db)&&pc[gc&da]===1))))
                        permit(1,ha,hb,"AND mixed driver");
                }
            }
        }
        if(pass){feasible++;const k=[pc[a],pc[b]].sort((x,y)=>x-y).join("+");
            hist[k]=(hist[k]??0)+1; if(examples.length<4)examples.push(pass);}
    }
    return {feasible,hist,examples};
}
function ordinaryRoot(u,h,budget) {
    const hist={};
    for(const {a,b,cross,ax,by,crossMask} of candidates(u)) {
        const hc=h&crossMask,c=hc?cross.find(v=>v[0]===hc):null;
        if(pc[hc]>1)continue;
        const A=(h|crossMask)&large[a],BB=(h|crossMask)&large[b];
        function test(ha,hb,op) {
            for(let k=lower(a,ha);k<=Math.min(budget-op-lower(b,hb),pc[a]-1);k++)
                if(possible(a,ha,k)&&possible(b,hb,budget-op-k))return true;
            return false;
        }
        let ok0=!c&&test(A,BB,0),ok1=false;
        for(const x of(c?[c[1]]:[...ax.keys(),0]))for(const y of(c?[c[2]]:[...by.keys(),0])){
            const da=(by.get(y)??0)&~h,db=(ax.get(x)??0)&~h, both=da&db&large[a]&large[b];
            const ca=A&~da,cb=BB&~db;
            if(test(ca|both,cb,1)||test(ca,cb|both,1))ok1=true;
        }
        if(ok0||ok1) {
            const key=[pc[a],pc[b]].sort((a,b)=>a-b).join("+")+"("+Number(ok0)+","+Number(ok1)+")";
            hist[key]=(hist[key]??0)+1;
        }
    }
    return hist;
}
const cases=[];
for(let h=through;;h=(h-1)&through) {
    const pass=possible(B,h,7);
    const root=pass?rootCommon(h):null;
    cases.push({singleWireTriples:h,count:pc[h],pass,root,first:pass?keep.get((B*N+h)*16+7):null});
    if(!h)break;
}
const chain={};
for(let drop=0;drop<7;drop++){
    const u=F&~((1<<drop)-1);
    chain[pc[u]]=ordinaryRoot(u,0,pc[u]-5);
}
const out={p,B,through,cases,chain,states:memo.size,subsets:cuts.size};
fs.writeFileSync(path.join(__dirname,process.argv.includes("--plain")?"budget-obligations-plain.json":"budget-obligations.json"),JSON.stringify(out,null,2)+"\n");
console.log(JSON.stringify({states:memo.size,subsets:cuts.size,
    histogram:cases.reduce((d,r)=>{let k=r.count+":"+r.pass;d[k]=(d[k]??0)+1;return d;},{})}));
