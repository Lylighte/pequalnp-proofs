"use strict";
const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const N=8192,F=N-1,lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,v)=>m|1<<((v+i)%13),0));
const pc=new Uint8Array(N);
for(let u=1;u<N;u++)pc[u]=1+pc[u&(u-1)];
const bin="D:/pequalnp-agent/tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe";
const dir=path.join(__dirname,"small-core");
fs.mkdirSync(dir,{recursive:true});
function image(u,k,t){let v=0;for(let i=0;i<13;i++)if(u&(1<<i))v|=1<<((k*i+t)%13);return v;}
function encode(u,helpers,omit=0,hard=0,prune=false,cover4=false) {
    const pts=Array.from({length:13},(_,i)=>1<<i).filter(p=>p&u);
    function remap(mask){return pts.reduce((v,b,i)=>v|((mask&b)?1<<i:0),0);}
    const n=pts.length,items=lines.map((l,i)=>({s:remap(l&u),native:Boolean(hard&(1<<i)),omit:Boolean(omit&(1<<i))})).filter(x=>!x.omit&&pc[x.s]>=(x.native?2:3)),targets=items.map(x=>x.s);
    const rows=Array.from({length:1<<n},(_,i)=>i).filter(i=>cover4?(pc[i]<=3||targets.includes(i)):pc[i]<=Math.max(...targets.map(s=>pc[s])));
    const clauses=[];let ctr=0;
    function v(){return ++ctr;}
    function literal(x,pol){return typeof x==="boolean"?(pol?x:!x):(pol?x:-x);}
    function clause(...ls){if(!ls.includes(true))clauses.push(ls.filter(x=>x!==false));}
    const vals=rows.map(r=>Array.from({length:n},(_,i)=>Boolean(r&(1<<i))));
    for(let h=0;h<helpers;h++) {
        const sides=[],menus=[];
        for(let side=0;side<2;side++) {
            const sels=Array.from({length:n+h},()=>v());
            menus.push(sels);
            sides.push(rows.map((r,ix)=>{
                const active=[];
                for(let j=0;j<n+h;j++){
                    const f=vals[ix][j];
                    if(f===false)continue;
                    if(f===true){active.push(sels[j]);continue;}
                    const a=v();clause(-a,sels[j]);clause(-a,f);clause(a,-sels[j],-f);active.push(a);
                }
                const o=v();for(const a of active)clause(-a,o);clause(-o,...active);return o;
            }));
        }
        if(prune){
            let prefix=true;
            for(let i=n+h-1;i>=0;i--){
                const a=menus[0][i],b=menus[1][i];
                clause(literal(prefix,false),-a,b);
                const eq=v();
                // Higher bits equal and this bit equal imply equality up to this position.
                clause(literal(prefix,false),-a,-b,eq);
                clause(literal(prefix,false),a,b,eq);
                prefix=eq;
            }
        }
        for(let i=0;i<rows.length;i++){const g=v(),a=sides[0][i],b=sides[1][i];
            clause(-g,a);clause(-g,b);clause(g,-a,-b);vals[i].push(g);}
    }
    const at=new Map(rows.map((r,i)=>[r,i]));
    if(cover4)for(let g=0;g<helpers;g++)clause(...rows.flatMap((r,i)=>pc[r]<=3?[vals[i][n+g]]:[]));
    for(const {s,native} of items) {
        if(prune)for(let sub=s;sub;sub=(sub-1)&s){
            const need=pc[sub]-(native?1:2);
            if(need<=0)continue;
            const labels=[];
            for(let j=0;j<helpers;j++){
                const flag=v(),slot=n+j;labels.push(flag);clause(-flag,vals[at.get(s)][slot]);
                for(let p=sub;p;p&=p-1) {
                    const except=p&-p,ds=[];
                    for(let q=sub^except;q;q&=q-1)ds.push(-vals[at.get(s^(q&-q))][slot]);
                    clause(-flag,...ds);
                }
            }
            if(need>helpers)clause();
            else for(let mask=0;mask<(1<<helpers);mask++)if(pc[mask]===helpers-need+1)
                clause(...labels.filter((_,j)=>mask&(1<<j)));
        }
        const options=[];
        for(let hi=n;hi<n+helpers;hi++)for(let lo=0;lo<=hi;lo++) {
            if(native&&lo!==hi)continue;
            if(lo<n&&!(s&(1<<lo)))continue;
            const choice=v();options.push(choice);
            for(let i=0;i<rows.length;i++){
                const r=rows[i],a=vals[i][lo],b=vals[i][hi];
                if(pc[r]>pc[s]||(cover4&&pc[r]===4&&r!==s))continue;
                if(r===s){clause(-choice,literal(a,true));clause(-choice,literal(b,true));}
                else clause(-choice,literal(a,false),literal(b,false));
            }
        }
        clause(...options);
    }
    return "p cnf "+ctr+" "+clauses.length+"\n"+clauses.map(c=>c.join(" ")+" 0").join("\n")+"\n";
}
function main(){
const count=Number(process.argv[2]??7),helpers=Number(process.argv[3]??2);
const only=Number(process.argv[4]??0);
const conflicts=Number(process.argv[5]??25000);
const json=path.join(dir,"results-"+count+"-"+helpers+(only?"-"+only:"")+(conflicts===25000?"":"-c"+conflicts)+".json");
const out=fs.existsSync(json)?JSON.parse(fs.readFileSync(json,"utf8")):{count,helpers,records:[]};
const seen=new Set(out.records.flatMap(r=>r.orbit));
for(let u=1;u<N;u++)if(pc[u]===count&&!seen.has(u)&&(!only||u===only)) {
    const orbit=[...new Set([1,3,9].flatMap(k=>Array.from({length:13},(_,t)=>image(u,k,t))))].sort((a,b)=>a-b);
    const file=path.join(dir,u+"-"+helpers+".cnf");
    fs.writeFileSync(file,encode(u,helpers));
    const cmd=cp.spawnSync(bin,["-q","-c",String(conflicts),file],{encoding:"utf8",timeout:45000,windowsHide:true});
    const verdict=cmd.status===10?"SAT":cmd.status===20?"UNSAT":"UNKNOWN";
    for(const s of orbit)seen.add(s);
    out.records.push({u,orbit,verdict});fs.writeFileSync(json,JSON.stringify(out)+"\n");
}
console.log(JSON.stringify(out.records.reduce((m,r)=>(m[r.verdict]=(m[r.verdict]??0)+r.orbit.length,m),{})));
}
module.exports={encode};
if(require.main===module)main();
