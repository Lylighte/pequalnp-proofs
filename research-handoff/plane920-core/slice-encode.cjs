const {lines}=require('./plane-symmetry.cjs'); const pc=Array.from({length:8192},(_,x)=>x.toString(2).replaceAll('0','').length);
function encode(u,helpers,forcedRows) {
    const pts=Array.from({length:13},(_,i)=>1<<i).filter(p=>p&u);
    function remap(mask){return pts.reduce((v,b,i)=>v|((mask&b)?1<<i:0),0);}
    const n=pts.length,targets=lines.map(l=>remap(l&u)).filter(s=>pc[s]>=3);
    const rows=forcedRows || Array.from({length:1<<n},(_,i)=>i).filter(i=>pc[i]<=Math.max(...targets.map(s=>pc[s])));
    const clauses=[];let ctr=0;
    function v(){return ++ctr;}
    function literal(x,pol){return typeof x==="boolean"?(pol?x:!x):(pol?x:-x);}
    function clause(...ls){if(!ls.includes(true))clauses.push(ls.filter(x=>x!==false));}
    const vals=rows.map(r=>Array.from({length:n},(_,i)=>Boolean(r&(1<<i))));
    for(let h=0;h<helpers;h++) {
        const sides=[];
        for(let side=0;side<2;side++) {
            const sels=Array.from({length:n+h},()=>v());
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
        for(let i=0;i<rows.length;i++){const g=v(),a=sides[0][i],b=sides[1][i];
            clause(-g,a);clause(-g,b);clause(g,-a,-b);vals[i].push(g);}
    }
    for(const s of targets) {
        const options=[];
        for(let hi=n;hi<n+helpers;hi++)for(let lo=0;lo<=hi;lo++) {
            if(lo<n&&!(s&(1<<lo)))continue;
            const choice=v();options.push(choice);
            for(let i=0;i<rows.length;i++){
                const r=rows[i],a=vals[i][lo],b=vals[i][hi];
                if(pc[r]>pc[s])continue;
                if(r===s){clause(-choice,literal(a,true));clause(-choice,literal(b,true));}
                else clause(-choice,literal(a,false),literal(b,false));
            }
        }
        clause(...options);
    }
    return "p cnf "+ctr+" "+clauses.length+"\n"+clauses.map(c=>c.join(" ")+" 0").join("\n")+"\n";
}

module.exports={encode};