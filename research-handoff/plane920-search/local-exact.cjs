const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict');
const outdir=__dirname,solver=path.resolve(outdir,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const base=[0,1,3,9],allLines=Array.from({length:13},(_,t)=>base.map(p=>(p+t)%13));
const pop=m=>{let n=0;for(;m;m&=m-1)n++;return n;};
function model(lineIDs,budget,extra,first=null){
 const actual=extra.lines||lineIDs.map(i=>allLines[i]),pts=[...new Set(actual.flat())].sort((a,b)=>a-b);
 const targets=actual.map(L=>L.reduce((s,v)=>s|1<<pts.indexOf(v),0));
 const n=pts.length,k=targets.length,hidden=budget-k;
 const choices=[],cnf=[];let vars=0;
 const fresh=()=>++vars;
 const clause=(...args)=>{if(args.includes(true))return;cnf.push(args.filter(x=>x!==false));};
 const neg=v=>typeof v==='boolean'?!v:-v;
 const one=arr=>{clause(...arr);for(let i=0;i<arr.length;i++)for(let j=0;j<i;j++)clause(-arr[i],-arr[j]);};
 for(let i=0;i<budget;i++){
   const count=n+Math.min(i,hidden),a=Array.from({length:count},fresh),b=Array.from({length:count},fresh),op=i<hidden?fresh():true;
   one(a);one(b);
   for(let x=0;x<count;x++)for(let y=0;y<=x;y++)clause(-a[x],-b[y]);
   choices.push({a,b,op});
 }
 if(first){clause(choices[0].a[first[0]]);clause(choices[0].b[first[1]]);clause(first[2]?choices[0].op:-choices[0].op);}
 if(extra.ops!==undefined)for(let i=0;i<hidden;i++)clause(extra.ops&(1<<i)?-choices[i].op:choices[i].op);
 if(extra.order)for(let i=first?2:1;i<hidden;i++){
   const old=choices[i-1],next=choices[i];
   for(let x=0;x<old.b.length;x++)for(let y=0;y<x;y++)clause(-old.b[x],-next.b[y]);
   for(let b=0;b<old.b.length;b++)for(let x=0;x<b;x++)for(let y=0;y<x;y++)
     clause(-old.b[b],-next.b[b],-old.a[x],-next.a[y]);
 }
 // Restrict to at least two genuine OR gates using the independent one-OR theorem.
 const ors=choices.slice(0,hidden).map(g=>g.op);
 if(extra.requireTwoOr)for(let omitted=0;omitted<ors.length;omitted++)clause(...ors.filter((_,i)=>i!==omitted).map(x=>-x));
 if(extra.live)for(let i=0;i<hidden;i++){
   const w=n+i;clause(...choices.slice(i+1).flatMap(g=>[g.a[w],g.b[w]]));
 }
 const seeds=new Set(targets);
 for(const L of targets)for(let v=0;v<n;v++)if(L&1<<v){
   seeds.add(L^1<<v);
   if(extra.swaps)for(let w=0;w<n;w++)if(!(L&1<<w))seeds.add((L^1<<v)|1<<w);
 }
 for(const s of extra.rows||[])seeds.add(s);
 const table=new Map(),coreRows=extra.core?pts.map((_,v)=>((1<<n)-1)^(1<<v)):[];
 for(const s of [...seeds,...coreRows]){
   const wires=pts.map((_,i)=>!!(s&1<<i));
   const end=seeds.has(s)?budget:hidden;
   for(let i=0;i<end;i++){
     const {a,b,op}=choices[i],s1=fresh(),s2=fresh(),out=i<hidden?fresh():s===targets[i-hidden];
     for(const [port,S] of [[a,s1],[b,s2]])for(let w=0;w<port.length;w++){
       clause(-port[w],neg(wires[w]),S);clause(-port[w],wires[w],-S);
     }
     // op=true AND; op=false OR. Terminal truth values are fixed.
     clause(neg(op),neg(out),s1);clause(neg(op),neg(out),s2);clause(neg(op),out,-s1,-s2);
     clause(op,out,-s1);clause(op,out,-s2);clause(op,neg(out),s1,s2);
     wires.push(out);
   }
   table.set(s,wires);
 }
 if(extra.core)for(let g=0;g<hidden;g++)for(let h=0;h<g;h++)for(const port of [choices[g].a,choices[g].b]){
   for(let x=0;x<n;x++)for(let y=0;y<x;y++)
     clause(choices[g].op,-port[n+h],table.get(coreRows[x])[n+h],table.get(coreRows[y])[n+h]);
 }
 if(extra.sensitivity)for(const L of targets){
   const eligible=[];
   for(let i=0;i<hidden;i++){
     const e=fresh();eligible.push(e);clause(-e,choices[i].op);clause(-e,table.get(L)[n+i]);
     const cut=pts.flatMap((_,v)=>L&1<<v?[neg(table.get(L^1<<v)[n+i])]:[]);
     for(let omit=0;omit<4;omit++)clause(-e,...cut.filter((_,j)=>j!==omit));
   }
   // Any AND/OR circuit sensitive to four raw points on L has three AND
   // merges there, and at most one of these is the line's terminal AND.
   for(let omit=0;omit<eligible.length;omit++)clause(...eligible.filter((_,j)=>j!==omit));
 }
 if(extra.sensitivity)for(const L of targets)for(const omit of pts.map((_,i)=>i).filter(i=>L&1<<i)){
   const triple=L^(1<<omit),candidates=[];
   for(let i=0;i<hidden;i++){
     const e=fresh();candidates.push(e);clause(-e,choices[i].op);clause(-e,table.get(L)[n+i]);
     const cut=pts.flatMap((_,v)=>triple&1<<v?[neg(table.get(L^1<<v)[n+i])]:[]);
     for(let j=0;j<3;j++)clause(-e,...cut.filter((_,h)=>h!==j));
   }
   clause(...candidates);
 }
 if(extra.privateBound)for(let T=1;T<(1<<k)-1;T++){
   const exclusive=[];
   for(let i=0;i<hidden;i++){
     const e=fresh();exclusive.push(e);
     clause(e,...targets.flatMap((L,t)=>T&(1<<t)?[]:[table.get(L)[n+i]]));
   }
   const cap=2*pop(T)-1;
   for(let M=0;M<1<<hidden;M++)if(pop(M)===cap+1)clause(...exclusive.flatMap((e,i)=>M&(1<<i)?[-e]:[]));
 }
 return {pts,targets,choices,cnf,vars,seeds:[...seeds]};
}
function test(lineIDs,budget,options={},first=null){
 const r=model(lineIDs,budget,options,first);
 const fn=path.join(outdir,'partial-'+lineIDs.join('-')+'-'+budget+'.cnf');
 const cs=r.cnf.map(c=>c.join(' ')+' 0').join('\n')+'\n';fs.writeFileSync(fn,'p cnf '+r.vars+' '+r.cnf.length+'\n'+cs);
 const lim=String(options.conflicts||20000);
 const start=Date.now();
 const sol=cp.spawnSync(solver,['-q','-c',lim,fn],{encoding:'utf8',windowsHide:true,timeout:options.ms||12000,maxBuffer:4<<20});
 if(sol.error)return {status:'TIMEOUT',ms:Date.now()-start};
 const result={status:sol.status===10?'SAT':sol.status===20?'UNSAT':'UNKNOWN',ms:Date.now()-start,
   vertices:r.pts.length,rows:r.seeds.length,vars:r.vars,clauses:r.cnf.length};
 if(sol.status===10){
   const yes=new Set(sol.stdout.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(/\s+/).map(Number)).filter(x=>x>0));
   const gates=r.choices.map(({a,b,op})=>[op===true||yes.has(op)?'&':'|',a.findIndex(v=>yes.has(v)),b.findIndex(v=>yes.has(v))]);
   const bad=[];
   for(let m=0;m<(1<<r.pts.length);m++)if(pop(m)<=(options.rowBudget||4)){
     const w=r.pts.map((_,i)=>!!(m&(1<<i)));
     gates.forEach(([op,a,b])=>w.push(op==='&'?w[a]&&w[b]:w[a]||w[b]));
     const o=w.slice(-lineIDs.length);if(o.some((t,i)=>t!==(m===r.targets[i])))bad.push(m);
   }
   assert(r.seeds.every(x=>!bad.includes(x)));Object.assign(result,{gates,points:r.pts,bad});
 }
 return result;
}
module.exports={model,test,allLines,pop};
if(require.main===module){
 const ids=process.argv[2].split(',').map(Number),n=Number(process.argv[3]),conflicts=Number(process.argv[4]||20000);
 const r=test(ids,n,{requireTwoOr:true,live:false,swaps:false,conflicts});
 console.log(JSON.stringify(r));
}
