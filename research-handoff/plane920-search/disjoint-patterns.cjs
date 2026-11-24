const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const n=12,k=4,hs=3,gs=[7,56,448,3584],pop=s=>{let n=0;for(;s;s&=s-1)n++;return n;};
const allowed=Array.from({length:4096},(_,i)=>i).filter(i=>pop(i)<=3),solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
function make(pat,rows){
 let vars=0;const cs=[],fresh=()=>++vars,neg=x=>typeof x==='boolean'?!x:-x;
 const clause=(...xs)=>{if(!xs.includes(true))cs.push(xs.filter(t=>t!==false));};
 const ports=Array.from({length:hs},(_,i)=>[0,1].map(()=>Array.from({length:n+i},fresh)));
 for(const m of rows){
   const w=Array.from({length:n},(_,i)=>!!(m&(1<<i)));
   for(const g of ports){
     const pair=g.map(p=>{
       const children=[];
       p.forEach((s,j)=>{if(w[j]===true)children.push(s);else if(w[j]!==false){
         const z=fresh();clause(-z,s);clause(-z,w[j]);clause(z,-s,-w[j]);children.push(z);}});
       const v=fresh();clause(-v,...children);for(const z of children)clause(-z,v);return v;
     });
     const v=fresh();clause(-v,pair[0]);clause(-v,pair[1]);clause(v,-pair[0],-pair[1]);w.push(v);
   }
   pat.forEach((t,i)=>{
     const pair=t<3?[i*3,n+t]:t===3?[n,n+1]:t===4?[n,n+2]:[n+1,n+2];
     if(gs[i]===m){clause(w[pair[0]]);clause(w[pair[1]]);}
     else clause(neg(w[pair[0]]),neg(w[pair[1]]));
   });
 }
 const dimacs='p cnf '+vars+' '+cs.length+'\n'+cs.map(c=>c.join(' ')+' 0').join('\n')+'\n';
 return {dimacs,ports};
}
const patterns=[];
for(let a=0;a<6;a++)for(let b=a;b<6;b++)for(let c=b;c<6;c++)for(let d=c;d<6;d++){
 const t=[a,b,c,d];if([3,4,5].some(y=>t.filter(x=>x===y).length>1))continue;patterns.push(t);
}
function verify(ports,pat,sol){
 const yes=new Set(sol.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(' ').map(Number)));
 const p=ports.map(g=>g.map(side=>side.reduce((w,s,j)=>w|(yes.has(s)?1<<j:0),0)));
 const bad=allowed.filter(m=>{
   let w=m;for(let i=0;i<hs;i++)if((p[i][0]&w)&&(p[i][1]&w))w|=1<<(n+i);
   return pat.some((t,i)=>{const b=t<3?[3*i,n+t]:t===3?[n,n+1]:t===4?[n,n+2]:[n+1,n+2];
     return (!!(w&1<<b[0])&&!!(w&1<<b[1]))!==(gs[i]===m);});
 });return {bad,p};
}
const initial=gs.flatMap(m=>[m,...Array.from({length:n},(_,j)=>m^(1<<j)).filter(v=>pop(v)===2)]);
const file=path.join(__dirname,'disjoint-pattern-results.json');
if(require.main===module){
 const old=fs.existsSync(file)?JSON.parse(fs.readFileSync(file,'utf8')):{rows:initial,results:[]};
 const rows=new Set(old.rows);const limit=Number(process.argv[2]||30000),maxMs=Number(process.argv[3]||60000),start=Date.now();
 for(const pat of patterns){
   if(Date.now()-start>maxMs)break;
   if(old.results.some(r=>r.status==='UNSAT'&&r.pat.join()===pat.join()))continue;
   for(let step=0;step<4;step++){
     const tested=[...rows],{dimacs,ports}=make(pat,tested),fn=path.join(__dirname,'disjoint-fixed.cnf');
     fs.writeFileSync(fn,dimacs);
     const p=cp.spawnSync(solver,['-q','-c',String(limit),fn],{encoding:'utf8',timeout:9000,windowsHide:true});
     const row={pat,status:p.status===20?'UNSAT':p.status===10?'SAT':'UNKNOWN',tested,sha256:crypto.createHash('sha256').update(dimacs).digest('hex')};
     old.results.push(row);
     if(p.status!==10)break;
     const v=verify(ports,pat,p.stdout);row.badCount=v.bad.length;row.wires=v.p;
     assert(tested.every(i=>!v.bad.includes(i)));if(!v.bad.length){console.log('WITNESS',row);break;}
     v.bad.slice(0,12).forEach(x=>rows.add(x));
   }
   old.rows=[...rows];fs.writeFileSync(file,JSON.stringify(old)+'\n');
 }
 const passed=new Set(old.results.filter(r=>r.status==='UNSAT').map(r=>r.pat.join()));
 console.log({patterns:patterns.length,passed:passed.size,left:patterns.length-passed.size,rows:rows.size,ms:Date.now()-start});
}
module.exports={make,patterns};
