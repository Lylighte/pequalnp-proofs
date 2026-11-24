const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),cp=require('node:child_process');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const line=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,x)=>m|1<<((x+i)%13),0));
const group=line.filter(l=>l&1).map(l=>l^1),cross=line.filter(l=>!(l&1));
const points=Array.from({length:12},(_,i)=>i+1),gSize=m=>points.filter(p=>m&1<<p).length;
const sparse=Array.from({length:8192},(_,m)=>m).filter(m=>!(m&1)&&gSize(m)<=2&&(gSize(m)<=1||(m&group[0])!==m));
function make(ops,mask,rs,support){
 let vars=0;const c=[],fresh=()=>++vars,neg=v=>typeof v==='boolean'?!v:-v,clause=(...ts)=>{if(!ts.includes(true))c.push(ts.filter(v=>v!==false));};
 const ps=ops.map((op,i)=>[0,1].map(()=>Array.from({length:12+i},fresh)));
 if(support){
   for(let j=0;j<12;j++)if(!(support&1<<(j+1))){for(const sides of ps)for(const p of sides)clause(-p[j]);}
   else clause(...ps.flatMap(sides=>sides.map(p=>p[j])));
   for(let j=0;j<ops.length-1;j++)clause(...ps.slice(j+1).flatMap(sides=>sides.map(p=>p[j+12])));
 }
 for(const sides of ps){
   for(const p of sides){
     clause(...p);for(let a=0;a<p.length;a++)for(let b=0;b<a;b++)clause(-p[a],-p[b]);
   }
   for(let a=0;a<sides[0].length;a++)for(let b=0;b<=a;b++)clause(-sides[0][a],-sides[1][b]);
 }
 const gr=[];
 for(const m of rs){
   const w=points.map(p=>!!(m&1<<p));
   for(let i=0;i<ops.length;i++){
     const [a,b]=ps[i].map(p=>{
       const s=fresh();for(let j=0;j<p.length;j++){clause(-p[j],-s,w[j]);clause(-p[j],s,neg(w[j]));}return s;
     });
     const z=fresh();
     if(ops[i]){clause(-z,a);clause(-z,b);clause(z,-a,-b);}
     else{clause(z,-a);clause(z,-b);clause(-z,a,b);}
     w.push(z);
   }
   const correct=m===group[0]||cross.some((L,j)=>L===m&&(mask&1<<j));clause(correct?w.at(-1):-w.at(-1));
   if(group.includes(m))gr.push(w.slice(12));
 }
 assert.equal(gr.length,4);
 for(let j=0;j<ops.length;j++)if(ops[j])clause(...gr.map(g=>g[j]));
 return {ps,dimacs:'p cnf '+vars+' '+c.length+'\n'+c.map(l=>l.join(' ')+' 0').join('\n')+'\n'};
}
const universe=[...new Set([...group,...cross,...sparse])],dir=path.join(__dirname,'endpoint-physical');fs.mkdirSync(dir,{recursive:true});
if(require.main===module){
 const nOR=Number(process.argv[2]||5),ms=Number(process.argv[3]||25000),slice=Number(process.argv[4]||500),file=path.join(dir,'results-'+nOR+'.json');
 const results=fs.existsSync(file)?JSON.parse(fs.readFileSync(file)):{};
 const masks=nOR===3?[7,19,21,38]:[7,19,21,38,15,23,39,53],start=Date.now(),orders=[];
 for(let a=0;a<nOR+2;a++)for(let b=a+1;b<nOR+2;b++)orders.push(Array.from({length:nOR+3},(_,i)=>Number(i===a||i===b||i===nOR+2)));
 orders.sort((a,b)=>{const score=x=>x.reduce((s,k,i)=>s+(k&&i!==nOR+2?Math.abs(i/(nOR+2)-0.5):0),0);return score(a)-score(b);});
 for(const ops of orders)for(const mask of masks){
   if(Date.now()-start>ms)break;
   const ans=results[mask]||={};if(Object.values(ans).some(v=>v.status==='SAT')||ans[ops.join('')]?.status==='UNSAT')continue;
   const key=ops.join(''),rs=ans[key]?.rows||[...group,...cross,...sparse.filter(m=>gSize(m)<=1)];
   for(let iter=0;iter<4;iter++){
     const {ps,dimacs}=make(ops,mask,rs),fn=path.join(dir,'current.cnf');fs.writeFileSync(fn,dimacs);
     const q=cp.spawnSync(solver,['-q','-c','15000',fn],{encoding:'utf8',windowsHide:true,timeout:slice});
     if(q.status!==10){ans[key]={status:q.status===20?'UNSAT':'UNKNOWN',rows:rs};break;}
     const yes=new Set(q.stdout.split(/\r?\n/).filter(x=>x.startsWith('v ')).flatMap(x=>x.slice(2).split(' ').map(Number)));
     const gates=ps.map(s=>s.map(p=>p.findIndex(k=>yes.has(k))));
     function evalOn(m){
       const w=points.map(p=>!!(m&1<<p));gates.forEach(([a,b],j)=>w.push(ops[j]?(w[a]&&w[b]):(w[a]||w[b])));return w.slice(12);
     }
     const bad=universe.filter(m=>evalOn(m).at(-1)!==(m===group[0]||cross.some((L,j)=>L===m&&!!(mask&1<<j))));
     assert(rs.every(m=>!bad.includes(m)));
     if(!bad.length){assert(ops.every((t,i)=>!t||group.some(m=>evalOn(m)[i])));ans[key]={status:'SAT',gates};break;}
     rs.push(...bad);ans[key]={status:'refine',rows:rs};
   }
   fs.writeFileSync(file,JSON.stringify(results)+'\n');
 }
 console.log(Object.fromEntries(Object.entries(results).map(([m,v])=>[m,Object.values(v).reduce((a,r)=>(a[r.status]=(a[r.status]||0)+1,a),{})])));
}
module.exports={make,universe};
