const {lines}=require('./plane-symmetry.cjs'); const pc=Array.from({length:8192},(_,x)=>x.toString(2).replaceAll('0','').length);
function encode(u,helpers,forcedRows,family) {
    const pts=Array.from({length:13},(_,i)=>1<<i).filter(p=>p&u);
    function remap(mask){return pts.reduce((v,b,i)=>v|((mask&b)?1<<i:0),0);}
    const n=pts.length,targets=(family ? family.lines : lines).map(l=>remap(l&u)).filter(s=>pc[s]>=3);
    const rows=forcedRows || Array.from({length:1<<n},(_,i)=>i).filter(i=>pc[i]<=Math.max(...targets.map(s=>pc[s])));
    const clauses=[],ports=[],decoders=[];let ctr=0;
    function v(){return ++ctr;}
    function literal(x,pol){return typeof x==="boolean"?(pol?x:!x):(pol?x:-x);}
    function clause(...ls){if(!ls.includes(true))clauses.push(ls.filter(x=>x!==false));}
    const vals=rows.map(r=>Array.from({length:n},(_,i)=>Boolean(r&(1<<i))));
    for(let h=0;h<helpers;h++) {
        const sides=[],selectors=[];ports.push(selectors);
        for(let side=0;side<2;side++) {
            const sels=Array.from({length:n+h},()=>v());selectors.push(sels);
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
        let tied=true;
        for(let j=0;j<n+h;j++){
            const x=selectors[0][j],y=selectors[1][j],next=v();
            clause(literal(tied,false),-x,y);
            clause(-next,tied);clause(-next,-x,y);clause(-next,x,-y);
            clause(literal(tied,false),x,y,next);clause(literal(tied,false),-x,-y,next);
            tied=next;
        }
        for(let i=0;i<rows.length;i++){const g=v(),a=sides[0][i],b=sides[1][i];
            clause(-g,a);clause(-g,b);clause(g,-a,-b);vals[i].push(g);}
    }
    if(family) {
        const at=new Map(rows.map((r,i)=>[r,i]));
        function requireCount(lits,k){
            if(k<=0)return;
            for(let mask=0;mask<(1<<lits.length);mask++)
                if(pc[mask]===lits.length-k+1)clause(...lits.filter((_,j)=>mask&(1<<j)));
        }
        for(let group=1;group<(1<<targets.length);group++){
            const size=pc[group],k=family.floors[Math.min(size,family.floors.length-1)];
            const labels=Array.from({length:helpers},(_,j)=>{
                const seen=v(),bits=targets.flatMap((t,i)=>(group&(1<<i))?[vals[at.get(t)][n+j]]:[]);
                clause(-seen,...bits);return seen;
            });
            requireCount(labels,k);
        }
        for(const s of targets)for(let sub=s;sub;sub=(sub-1)&s){
            const need=pc[sub]-2;
            if(need<=0)continue;
            const labels=Array.from({length:helpers},(_,j)=>{
                const label=v();clause(-label,vals[at.get(s)][n+j]);
                for(let p=sub;p;p&=p-1){
                    const rest=sub^(p&-p),disabled=[];
                    for(let q=rest;q;q&=q-1)disabled.push(-vals[at.get(s^(q&-q))][n+j]);
                    clause(-label,...disabled);
                }
                return label;
            });
            requireCount(labels,need);
        }
    }
    for(const s of targets) {
        const options=[],defs=[];decoders.push({s,defs});
        for(let hi=n;hi<n+helpers;hi++)for(let lo=0;lo<=hi;lo++) {
            if(lo<n&&!(s&(1<<lo)))continue;
            const choice=v();options.push(choice);defs.push({choice,lo,hi});
            for(let i=0;i<rows.length;i++){
                const r=rows[i],a=vals[i][lo],b=vals[i][hi];
                if(pc[r]>pc[s])continue;
                if(r===s){clause(-choice,literal(a,true));clause(-choice,literal(b,true));}
                else clause(-choice,literal(a,false),literal(b,false));
            }
        }
        clause(...options);
    }
    const cnf="p cnf "+ctr+" "+clauses.length+"\n"+clauses.map(c=>c.join(" ")+" 0").join("\n")+"\n";
    return {cnf,ports,decoders,n,targets,vals};
}
module.exports={encode};
