const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),cp=require('node:child_process'),zlib=require('node:zlib');
const {checkProof}=require('./stream-rup.cjs');
const solver=path.resolve(__dirname,'../../tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe');
const points=n=>Array.from({length:n},(_,i)=>i);
function encode(n,h,rawPattern,plainPattern,rows,derived=false,saturate=false,firstPorts,firstExact){
 let vars=0;const clauses=[],fresh=()=>++vars;
 const neg=t=>typeof t==='boolean'?!t:-t;
 function clause(...xs){if(!xs.includes(true))clauses.push(xs.filter(v=>v!==false));}
 const gate=Array.from({length:h},(_,i)=>[0,1].map(()=>Array.from({length:n+i},fresh)));
 if(firstPorts)for(let side=0;side<2;side++)for(const j of firstPorts[side])clause(gate[0][side][j]);
 if(firstExact)for(let side=0;side<2;side++)for(let j=0;j<n;j++)clause((firstExact[side]&1<<j)?gate[0][side][j]:-gate[0][side][j]);
 const shared=Array.from({length:n+h},fresh);
 const halfPairs=[];for(let a=0;a<h;a++)for(let b=a+1;b<h;b++)halfPairs.push([n+a,n+b]);
 function or(port,w){
   const ss=[];
   for(let j=0;j<port.length;j++)if(w[j]!==false){
     if(w[j]===true)ss.push(port[j]);
     else{const s=fresh();clause(-s,port[j]);clause(-s,w[j]);clause(s,-port[j],-w[j]);ss.push(s);}
   }
   const z=fresh();for(const s of ss)clause(-s,z);clause(-z,...ss);return z;
 }
 const positives=[];
 for(const m of rows){
   const w=points(n).map(i=>!!(m&1<<i));
   for(let i=0;i<h;i++){
     const a=or(gate[i][0],w),b=or(gate[i][1],w),z=fresh();
     clause(-z,a);clause(-z,b);clause(z,-a,-b);w.push(z);
   }
   const f=or(shared,w),outs=rawPattern.map((t,i)=>[f,w[t===0?i*3:n+t-1]]);
   if(saturate)for(let i=0;i<(saturate==='three'?3:4);i++)if(m===(7<<(3*i)))positives[i]=w.slice(n);
   if(derived&&m.toString(2).replaceAll('0','').length<=2){
     for(let i=0;i<rawPattern.length;i++)if(rawPattern[i]===0&&(m|1<<(3*i))!==(7<<(3*i)))clause(-f);
     for(let i=0;i<plainPattern.length;i++)if(plainPattern[i]<h){
       const j=i+2;if((m|1<<(3*j))!==(7<<(3*j)))clause(-w[n+plainPattern[i]]);
     }
   }
   plainPattern.forEach((t,i)=>{const pair=t<h?[(i+2)*3,n+t]:halfPairs[t-h];outs.push(pair.map(v=>w[v]));});
   outs.forEach(([a,b],i)=>{if(m===(7<<(i*3))){clause(a);clause(b);}else clause(neg(a),neg(b));});
 }
 if(saturate==='three'){
   assert(h===4&&n===9&&rawPattern.join()==='0,0,0');
   for(let j=0;j<h;j++)for(let a=0;a<3;a++)for(let b=0;b<a;b++)clause(positives[a][j],positives[b][j]);
   for(let k=0;k<n+h;k++)clause(k===n+3?shared[k]:-shared[k]);
 }else if(saturate){
   assert(h===4&&rawPattern.join()==='0,0'&&plainPattern.join()==='3,3');
   for(let j=0;j<h;j++){clause(positives[0][j],positives[1][j]);clause(positives[2][j],positives[3][j]);}
   clause(shared[n+3]);
 }
 return {dimacs:'p cnf '+vars+' '+clauses.length+'\n'+clauses.map(c=>c.join(' ')+' 0').join('\n')+'\n',gate,shared};
}
function verify(model,n,rawPattern,plainPattern,rows){
 const {gate,shared}=model,h=gate.length;
 const pairs=[];for(let a=0;a<h;a++)for(let b=a+1;b<h;b++)pairs.push([n+a,n+b]);
 return rows.filter(m=>{
   let w=m;for(let i=0;i<h;i++)if((gate[i][0]&w)&&(gate[i][1]&w))w|=1<<(n+i);
   const f=!!(w&shared),out=rawPattern.map((t,i)=>f&&!!(w&1<<(t===0?3*i:n+t-1)));
   plainPattern.forEach((t,i)=>{const [a,b]=t<h?[(i+2)*3,n+t]:pairs[t-h];out.push(!!(w&1<<a)&&!!(w&1<<b));});
   return out.some((v,i)=>v!==(m===(7<<(3*i))));
 });
}
const rows=n=>points(1<<n).filter(m=>m.toString(2).replaceAll('0','').length<=3);
const code=(sol,arr)=>{const yes=new Set(sol.split(/\r?\n/).filter(l=>l.startsWith('v ')).flatMap(l=>l.slice(2).split(' ').map(Number)));
 const mask=s=>s.reduce((a,x,j)=>a|(yes.has(x)?1<<j:0),0);
 return {gate:arr.gate.map(g=>g.map(mask)),shared:mask(arr.shared)};
};
if(require.main===module)(async()=>{
 const dir=path.join(__dirname,'common-two-replay');fs.mkdirSync(dir,{recursive:true});
 const reports=[];
 for(const h of [2,3,4])for(let a=0;a<=h;a++)for(let b=a;b<=h;b++){
   if(a&&a===b)continue;
   const pat=[a,b],r=rows(6),instance=encode(6,h,pat,[],r),f=path.join(dir,'active.cnf'),pf=path.join(dir,'active.lrat');
   fs.writeFileSync(f,instance.dimacs);
   const run=cp.spawnSync(solver,['-q','--plain','--lrat','--no-binary',f,pf],{encoding:'utf8',timeout:7500,windowsHide:true});
   const row={h,pat};if(run.status===10){const model=code(run.stdout,instance);assert.equal(verify(model,6,pat,[],r).length,0);Object.assign(row,{status:'SAT',model});}
   else if(run.status===20){
     const p=await checkProof(instance.dimacs,pf),gzip=zlib.gzipSync(fs.readFileSync(pf)),name=[h,a,b].join('')+'.lrat.gz';
     fs.writeFileSync(path.join(dir,name),gzip);Object.assign(row,{status:'UNSAT',name,bytes:gzip.length,...p});
   }else row.status='UNKNOWN';
   reports.push(row);if(h===4&&row.status==='SAT')break;
 }
 fs.writeFileSync(path.join(dir,'results.json'),JSON.stringify(reports,null,2)+'\n');console.log(reports.map(({h,pat,status})=>[h,pat.join(''),status]));
})().catch(e=>{console.error(e);process.exitCode=1;});
module.exports={encode,verify,code,rows};
