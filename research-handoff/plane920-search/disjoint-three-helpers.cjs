const fs=require('node:fs'),path=require('node:path'),cp=require('node:child_process'),assert=require('node:assert/strict');
const groups=[7,56,448,3584],n=12,hidden=3,k=4;
const pop=s=>{let n=0;for(;s;s&=s-1)n++;return n;};
const allowed=Array.from({length:1<<n},(_,i)=>i).filter(m=>pop(m)<=3);
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
function synth(rows,limit){
 let vars=0;const cs=[],fresh=()=>++vars,neg=a=>typeof a==='boolean'?!a:-a;
 function clause(...l){if(l.includes(true))return;cs.push(l.filter(t=>t!==false));}
 const ports=Array.from({length:hidden+k},(_,i)=>Array.from({length:2},()=>Array.from({length:n+Math.min(i,hidden)},fresh)));
 for(const m of rows){
   const w=Array.from({length:n},(_,j)=>!!(m&(1<<j)));
   for(let i=0;i<ports.length;i++){
     const sv=ports[i].map(port=>{
       const sources=[];
       for(let j=0;j<port.length;j++)if(w[j]!==false){
         if(w[j]===true)sources.push(port[j]);
         else{const z=fresh();clause(-z,port[j]);clause(-z,w[j]);clause(z,-port[j],-w[j]);sources.push(z);}
       }
       const s=fresh();clause(-s,...sources);for(const z of sources)clause(-z,s);return s;
     });
     const val=i<hidden?fresh():m===groups[i-hidden];clause(neg(val),sv[0]);clause(neg(val),sv[1]);clause(val,-sv[0],-sv[1]);
     w.push(val);
   }
 }
 const fn=path.join(__dirname,'disjoint3helpers.cnf');fs.writeFileSync(fn,'p cnf '+vars+' '+cs.length+'\n'+cs.map(c=>c.join(' ')+' 0').join('\n')+'\n');
 const start=Date.now(),p=cp.spawnSync(solver,['-q','-c',String(limit),fn],{encoding:'utf8',timeout:20000,windowsHide:true});
 if(p.status!==10)return {status:p.status===20?'UNSAT':'UNKNOWN',rows:rows.length,ms:Date.now()-start};
 const yes=new Set(p.stdout.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(' ').map(Number)));
 const gs=ports.map(g=>g.map(port=>port.reduce((a,s,j)=>a|(yes.has(s)?1<<j:0),0)));
 const bad=allowed.filter(m=>{
   let w=m;for(let i=0;i<gs.length;i++)if((gs[i][0]&w)&&(gs[i][1]&w))w|=1<<(n+i);
   return groups.some((g,i)=>!!(w&(1<<(n+hidden+i)))!==(m===g));
 });
 assert(rows.every(m=>!bad.includes(m)));return {status:'SAT',gates:gs,bad,rows:rows.length,ms:Date.now()-start};
}
const initial=groups.flatMap(m=>[m,...Array.from({length:12},(_,i)=>m^(1<<i)).filter(t=>pop(t)===2)]);
const rows=new Set(initial),results=[];
for(let i=0;i<12;i++){
 const r=synth([...rows],50000);results.push({...r,bad:r.bad?.length});console.log(i,r.status,r.ms,r.rows,r.bad?.length);
 if(r.status!=='SAT'||!r.bad.length)break;
 for(const j of r.bad.slice(0,35))rows.add(j);
}
fs.writeFileSync(path.join(__dirname,'disjoint3helpers.json'),JSON.stringify({rows:[...rows],results},null,2)+'\n');
