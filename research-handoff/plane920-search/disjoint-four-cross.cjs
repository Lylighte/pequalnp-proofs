const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict');
const n=12,h=4,targets=[7,56,448,3584],points=Array.from({length:n},(_,i)=>i);
const bits=m=>points.filter(i=>(m&1<<i)!==0);
const allowed=Array.from({length:4096},(_,i)=>i).filter(m=>bits(m).length<=3);
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const halves=[[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]];
const pair=(t,i)=>t<4?[3*i,12+t]:halves[t-4].map(x=>12+x);
const cross=allowed.filter(m=>{const q=bits(m);return q.length===2&&q[0]%3!==2&&q[1]%3!==2&&(q[0]/3|0)!==(q[1]/3|0);});
assert.equal(cross.length,24);
function make(pat,rows,needCross=true,pinned){
 let vars=0;const clauses=[],fresh=()=>++vars,neg=x=>typeof x==='boolean'?!x:-x;
 function clause(...l){if(!l.includes(true))clauses.push(l.filter(x=>x!==false));}
 const ports=Array.from({length:h},(_,g)=>[0,1].map(()=>Array.from({length:n+g},fresh)));
 const activations=[];
 for(const m of rows){
   const w=points.map(i=>!!(m&1<<i));
   for(let i=0;i<h;i++){
     const children=ports[i].map(p=>{
       const list=[];
       for(let j=0;j<p.length;j++)if(w[j]!==false){
         if(w[j]===true)list.push(p[j]);else{
           const z=fresh();clause(-z,p[j]);clause(-z,w[j]);clause(z,-p[j],-w[j]);list.push(z);
         }
       }
       const z=fresh();clause(-z,...list);for(const s of list)clause(-s,z);return z;
     });
     const v=fresh();clause(-v,children[0]);clause(-v,children[1]);clause(v,-children[0],-children[1]);w.push(v);
     if(needCross&&cross.includes(m)){
       if(pat.includes(i))clause(-v);
       else activations.push(v);
       if(pinned&&m===pinned.mask&&i<=pinned.helper)clause(i===pinned.helper?v:-v);
     }
   }
   for(let i=0;i<4;i++){
     const [a,b]=pair(pat[i],i);
     if(m===targets[i]){clause(w[a]);clause(w[b]);}else clause(neg(w[a]),neg(w[b]));
   }
 }
 if(needCross)clause(...activations);
 return {ports,dimacs:'p cnf '+vars+' '+clauses.length+'\n'+clauses.map(c=>c.join(' ')+' 0').join('\n')+'\n'};
}
const patterns=[];
for(let a=0;a<10;a++)for(let b=a;b<10;b++)for(let c=b;c<10;c++)for(let d=c;d<10;d++){
 const p=[a,b,c,d];if(p.some((v,i)=>v>=4&&p.indexOf(v)!==i))continue;patterns.push(p);
}
function evaluate(ports,pat,m){
 let w=m;for(let i=0;i<h;i++)if((ports[i][0]&w)&&(ports[i][1]&w))w|=1<<(12+i);
 const errors=pat.map((t,i)=>{const [a,b]=pair(t,i);return (!!(w&1<<a)&&!!(w&1<<b))!==(targets[i]===m);});
 return {bad:errors.includes(true),active:w>>12};
}
function check(ports,pat,m){
 const yes=new Set(m.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(' ').map(Number)));
 const masks=ports.map(g=>g.map(s=>s.reduce((z,id,j)=>z|(yes.has(id)?1<<j:0),0)));
 const bad=allowed.filter(m=>evaluate(masks,pat,m).bad);
 return {masks,bad,crossActive:cross.filter(m=>evaluate(masks,pat,m).active)};
}
if(require.main===module){
 const file=path.join(__dirname,'disjoint-four-cross-results.json');
 const state=fs.existsSync(file)?JSON.parse(fs.readFileSync(file)):{rows:[...new Set([...cross,...targets,...targets.flatMap(t=>bits(t).map(i=>t^(1<<i)))])],results:{}};
 const started=Date.now(),maxMs=Number(process.argv[2]||45000);
 const order=patterns.slice().sort((a,b)=>new Set(b.filter(x=>x<4)).size-new Set(a.filter(x=>x<4)).size);
 const attempts={};
 for(const pat of order){
   if(Date.now()-started>maxMs)break;
   const key=pat.join(',');
   if(['UNSAT','SAT','analytic'].includes(state.results[key]?.status))continue;
   if(new Set(pat.filter(x=>x<4)).size===4){state.results[key]={status:'analytic'};continue;}
   for(let i=0;i<5&&Date.now()-started<=maxMs;i++){
     const rows=state.rows.slice(),{ports,dimacs}=make(pat,rows);
     const filename=path.join(__dirname,'disjoint-four-cross-active.cnf');fs.writeFileSync(filename,dimacs);
     const s=cp.spawnSync(solver,['-q','-c','50000',filename],{encoding:'utf8',timeout:3000,windowsHide:true});
     const status=s.status===20?'UNSAT':s.status===10?'SAT':'UNKNOWN';
     attempts[status]=(attempts[status]||0)+1;
     if(status==='UNSAT'){state.results[key]={status,rows:rows.length};break;}
     if(status==='UNKNOWN'){state.results[key]={status};break;}
     const v=check(ports,pat,s.stdout);
     assert(v.crossActive.length);assert(!rows.some(m=>v.bad.includes(m)));
     if(!v.bad.length){state.results[key]={status,masks:v.masks,crossActive:v.crossActive};break;}
     state.rows.push(...v.bad.slice(0,16));
   }
   fs.writeFileSync(file,JSON.stringify(state)+'\n');
   if(state.results[key]?.status==='SAT')break;
 }
 const summary=Object.values(state.results).reduce((o,e)=>(o[e.status]=(o[e.status]||0)+1,o),{});console.log({patterns:patterns.length,summary,rows:state.rows.length,elapsed:Date.now()-started,attempts,sat:Object.entries(state.results).filter(([k,v])=>v.status==='SAT')});
}
module.exports={make,patterns,cross,evaluate,allowed};
