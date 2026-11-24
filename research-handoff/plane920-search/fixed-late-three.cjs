const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {record,getArms,join,signature,fixed}=require('../plane920-core/unrestricted-prefix.cjs');
const {table,lines,pc}=require('./three-or-five-lines.cjs'),{inspect}=require('./private-independent.cjs');
const root=path.join(__dirname,'../plane920-core/unrestricted'),all=8191;
const monomial=[0,all,...lines.map((_,j)=>1<<j),...lines.map((_,j)=>lines.reduce((s,L,i)=>s|(L&1<<j?1<<i:0),0))];
function inputs(){
 const a=[];
 for(const n of fs.readdirSync(root).filter(n=>/^round-27-5678-.*\.jsonl$/.test(n))){
   for(const line of fs.readFileSync(path.join(root,n),'utf8').trim().split('\n').filter(Boolean)){
     const z=JSON.parse(line);for(const [i,j,hs] of z.live)if(hs.includes(8))a.push([z.id,i,j]);
   }
 }
 return a.sort((a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2]);
}
function game(pos,cost,forced,floor,searchBudget=1e6){
 let opened=0,comparisons=0,short=false;
 const sig=new Set(monomial);
 for(const a of pos)for(const b of [...sig])sig.add(a&b);
 sig.delete(0);sig.delete(all);const base=[...sig].sort((a,b)=>pc[b]-pc[a]);
 const charge=cost.map((v,i)=>Math.max(v,floor[i]||0)),delta=charge.map((c,i)=>c-(floor[i]||0));
 const baseFloor=floor.reduce((a,b)=>a+b,0),budget=6-forced-baseFloor;
 const counts=[0,1,2].map(c=>charge.reduce((m,v,i)=>m|(c===v?1<<i:0),0)),d1=delta.reduce((m,v,i)=>m|(v>=1?1<<i:0),0),d2=delta.reduce((m,v,i)=>m|(v>=2?1<<i:0),0);
 const w=m=>pc[m&d1]+pc[m&d2];
 const leaf=new Int8Array(8192),a1=new Int8Array(8192),a2=new Int8Array(8192);
 function fits(m){
   if(leaf[m])return leaf[m]===1;
   const t=w(m);let ok=t<=budget;
   if(ok && t===budget&&!forced&&2*pc[m]>6)ok=false;
   if(ok){
     const c=[];for(let i=0;i<13;i++)if(m&1<<i)c.push(charge[i]);c.sort((x,y)=>x-y);
     let r=0;for(let i=0;i<Math.min(3,c.length);i++){
       r+=c[i];if(t+baseFloor-r+[2,4,5][i]>6){ok=false;break;}
     }
   }
   leaf[m]=ok?1:-1;return ok;
 }
 function adaptive(m,d){
   if(fits(m))return true;if(!d||w(m)>budget*(1<<d))return false;
   const memo=d===1?a1:a2;
   if(memo[m])return memo[m]===1;
   const ans=()=>{
     if(d>1&&adaptive(m,d-1))return true;
     const arms=base.filter(a=>adaptive(m&~a,d-1));
     for(let i=0;i<arms.length;i++)for(let j=0;j<i;j++){
       const a=arms[i],b=arms[j];
       if(adaptive(m&(~a|b),d-1)&&adaptive(m&(~b|a),d-1))return true;
     }
     return false;
   };
   const v=ans();memo[m]=v?1:-1;return v;
 }
 // After selecting fixed input arms, retain every positive row on which
 // each replaced OR keeps its original value. The two child signatures for
 // a future, unmodified OR may also include all preceding unmodified ORs.
 function visit(sets,domain,depth){
   sets=[...new Set(sets)].filter(m=>!fits(m)).sort((a,b)=>pc[b]-pc[a]);
   sets=sets.filter((m,i)=>!sets.slice(0,i).some(t=>(m&t)===m));
   if(!sets.length)return [];
   if(opened++>=searchBudget){short=true;return null;}
   const arms=domain.filter(a=>sets.every(m=>adaptive(m&~a,depth-1)));
   for(let i=1;i<arms.length;i++)for(let j=0;j<i;j++){
     comparisons++;const a=arms[i],b=arms[j],x=a&~b,y=b&~a;
     if(!x||!y)continue;
     const next=[];
     let ok=true;
     for(const s of sets){
       const r=s&~x,t=s&~y;
       if(!adaptive(r,depth-1)||!adaptive(t,depth-1)){ok=false;break;}
       next.push(r,t);
     }
     if(!ok)continue;
     if(depth===1)return [[a,b]];
     const u=a|b,newDomain=new Set(domain);newDomain.add(u);
     for(const s of domain){const v=s&u;if(v)newDomain.add(v);}
     const more=visit(next,[...newDomain],depth-1);
     if(more)return [[a,b],...more];
     if(short)return null;
   }
   return null;
 }
 const witness=visit([all],base,3);
 return {verdict:witness?'open':short?'cutoff':'excluded',witness,opened,comparisons};
}
if(require.main===module){
 const from=Number(process.argv[2]||0),n=Number(process.argv[3]||100),max=Number(process.argv[4]||1e6),dir=path.join(__dirname,'fixed-late-three');fs.mkdirSync(dir,{recursive:true});
 const filename=path.join(dir,'input-snapshot.json');
 let candidates;
 if(process.argv.includes('--snapshot')){
   if(!fs.existsSync(filename))fs.writeFileSync(filename,JSON.stringify(inputs())+'\n');
   candidates=JSON.parse(fs.readFileSync(filename));
 }else candidates=inputs();
 const batch=candidates.slice(from,from+n);
 const outfile=path.join(dir,from+'-'+n+'.jsonl'),done=new Map();
 if(fs.existsSync(outfile))for(const t of fs.readFileSync(outfile,'utf8').trim().split('\n').filter(Boolean)){const z=JSON.parse(t);done.set(z.id.join(','),z);}
 const cache=new Map();let src,last=-1,arms,start=Date.now();
 for(const id of batch){
   if(done.has(id.join(',')))continue;
   const [p,i,j]=id;if(p!==last){src=record(p);arms=getArms(src.gates);last=p;}
   const pair=[arms[i],arms[j]],fifth=join(...pair),gates=[...src.gates,fifth],f=fixed(gates,[...src.pairs,pair]);
   assert(!f.dominated);const os=gates.map(signature),c=inspect(gates.map(table),100).costs;
   const pos=os.map(g=>g.active),key=pos.join(',')+'/'+c.join('')+'/'+f.shared+'/'+f.priv.join(',');
   if(!cache.has(key))cache.set(key,game(pos,c,f.shared,f.priv,max));
   const res={id,...cache.get(key)};fs.appendFileSync(outfile,JSON.stringify(res)+'\n');done.set(id.join(','),res);
 }
 const totals={};for(const e of done.values())totals[e.verdict]=(totals[e.verdict]||0)+1;
 console.log({from,n,totals,cache:cache.size,ms:Date.now()-start});
}
module.exports={game,inputs};
