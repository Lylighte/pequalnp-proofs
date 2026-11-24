const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const bits=m=>{const v=[];for(let i=0;m;m>>>=1,i++)if(m&1)v.push(i);return v;};
const line=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,x)=>m|1<<((x+i)%13),0));
const group=line.filter(l=>l&1).map(l=>l^1),cross=line.filter(l=>!(l&1)),full=8190;
const points=bits(full),ptSets=points.map(p=>cross.reduce((m,L,i)=>m|((L&1<<p)?1<<i:0),0));
const coords=cross.map(L=>group.slice(0,2).map(g=>bits(g).indexOf(bits(L&g)[0])));
assert.equal(new Set(coords.map(c=>c.join())).size,9);
const perm=[];
for(const a of [1,2])for(const e of [1,2])for(let c=0;c<3;c++)for(let d=0;d<3;d++)for(let f=0;f<3;f++){
 const p=coords.map(([x,y])=>coords.findIndex(([u,v])=>u===(a*x+c)%3&&v===(d*x+e*y+f)%3));
 assert.equal(new Set(p).size,9);
 const transform=m=>p.reduce((v,j,i)=>v|((m&1<<i)?1<<j:0),0);
 assert(ptSets.every(s=>ptSets.includes(transform(s))));
 assert(bits(group[0]).every(j=>bits(group[0]).some(k=>ptSets[k-1]===transform(ptSets[j-1]))));
 perm.push(transform);
}
const prime=ts=>[...new Set(ts)].filter((m,_,vs)=>!vs.some(v=>v!==m&&(v&m)===v)).sort((a,b)=>a-b);
function syntaxes(n){
 const shapes=new Map(),fan=2*n+1;
 function combine(base,dep,os){
   let terms=[1<<base];for(const k of bits(dep))terms=prime(terms.flatMap(t=>os[k].map(u=>t|u)));
   return terms;
 }
 function walk(os){
   const i=os.length;
   if(i===n){
     for(let d=0;d<1<<n;d++){
       const t=combine(2*n,d,os);shapes.set(t.join(','),t);
     }
     return;
   }
   for(let a=0;a<1<<i;a++)for(let b=0;b<=a;b++)
     walk([...os,prime([...combine(2*i,a,os),...combine(2*i+1,b,os)])]);
 }
 walk([]);return [...shapes.values()].map(terms=>({terms,indices:terms.map(bits),fan}));
}
const cardinal=Array.from({length:8192},(_,i)=>bits(i).length);
function solve(n,mask){
 const wanted=[group[0],...bits(mask).map(i=>cross[i])],neg=[...group.slice(1),...cross.filter((_,i)=>!(mask&1<<i))];
 const shapes=syntaxes(n),positive=wanted.length;
 let tries=0,found;
 for(const {terms,indices,fan} of shapes){
   if(terms.length<positive)continue;
   const assigned=[];
   function act(i,used){
     if(i<positive){
       for(let t=0;t<terms.length;t++)if(!(used&1<<t)){
         assigned.push(t);act(i+1,used|1<<t);assigned.pop();if(found)return;
       }
       return;
     }
     tries++;const atoms=new Int32Array(fan).fill(full);
     for(let j=0;j<positive;j++)for(const a of indices[assigned[j]])atoms[a]&=wanted[j];
     const supports=indices.map(ix=>ix.reduce((v,j)=>v|atoms[j],0));
     if(supports.some(s=>cardinal[s]<2||(cardinal[s]===2&&(s&group[0])!==s)||neg.some(v=>(s&v)===s)))return;
     found={terms,assigned:[...assigned],atoms:[...atoms],supports}; 
   }
   act(0,0);if(found)break;
 }
 return {n,mask,tries,found:found||null};
}
const args=process.argv.slice(2).map(Number),n=args[0]||3,degrees=args[1]?[args[1]]:[3,4],runs=[];
for(const d of degrees){
 const seen=new Set();
 for(let mask=0;mask<512;mask++){
   if(cardinal[mask]!==d||seen.has(mask))continue;
   const orbit=new Set(perm.map(p=>p(mask)));for(const u of orbit)seen.add(u);
   runs.push({...solve(n,mask),orbit:orbit.size});
 }
 assert.equal(seen.size,d===3?84:126);
}
fs.writeFileSync(path.join(__dirname,'endpoint-or-'+n+'-'+degrees.join('')+'.json'),JSON.stringify(runs,null,2)+'\n');
console.log(runs.map(r=>[r.mask,r.orbit,r.tries,!!r.found]));
