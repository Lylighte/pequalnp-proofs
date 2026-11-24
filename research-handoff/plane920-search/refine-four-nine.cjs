const fs=require('node:fs'),path=require('node:path');
const {table,mult,join,raw,pm,univ}=require('./three-or-five-lines.cjs'),{pricedTables}=require('./paid-or-arms.cjs');
const cache=new Map();
function choices(prev,target){
 const key=prev.map(t=>t.join(',')).join('/')+'//'+target.toString(16);if(cache.has(key))return cache.get(key);
 const ps=[univ];for(const f of prev.map(table))for(const v of [...ps])ps.push(v&f);
 const opts=new Map();for(let p=-1;p<13;p++)for(let j=0;j<ps.length;j++){
  if(p<0&&!j)continue;const v=(p<0?univ:raw[p])&ps[j];if(v===target||(v&target)!==v||opts.has(v))continue;opts.set(v,pm(v));
 }
 const arr=[...opts],pairs=[];
 for(let i=0;i<arr.length;i++)for(let j=0;j<i;j++){
   const [v,a]=arr[i],[w,b]=arr[j];if((a&~b)&&(b&~a)&&(v|w)===target)pairs.push([v,w]);
 }
 cache.set(key,pairs);return pairs;
}
function check(row){
 const gs=row.terms,arm=([p,j])=>gs.reduce((w,t,i)=>j&1<<i?w&table(t):w,p<0?univ:raw[p]);
 const final=arm(row.a)|arm(row.b),flags=[...gs.map(table),final],pairs=flags.map((v,i)=>choices(gs.slice(0,i),v));
 let num=0,open=null;const seen=new Set();
 function go(i,known,paid,cuts){
  if(open)return;
  if(i===4){
   const k=[...paid].map(v=>v.toString(16)).sort().join('/')+'//'+cuts.join(',');
   if(seen.has(k))return;seen.add(k);num++;
   const r=pricedTables(flags,[...paid],6,9,0,1,cuts,true);
   if(r.found)open={paid:[...paid].map(v=>v.toString(16)),cuts,r};
   return;
  }
  for(const [a,b] of pairs[i]){
    const f=new Set(paid);for(const t of [a,b])if(!known.has(t))f.add(t);
    const x=pm(a),y=pm(b);go(i+1,new Set([...known,flags[i]]),f,[...cuts,x&~y,y&~x]);if(open)return;
  }
 }
 go(0,new Set(raw),new Set(),[]);return {num,open};
}
if(require.main===module){
 const file=process.argv[2]||'four-or-6lines-9-shared-0-1897.json';
 const ds=JSON.parse(fs.readFileSync(path.join(__dirname,file))).survivors,report=[];
 for(let i=0;i<ds.length;i++){const r=check(ds[i]);report.push({i,...r});}
 const result={size:ds.length,checked:report.reduce((n,v)=>n+v.num,0),surviving:report.filter(x=>x.open)};
 fs.writeFileSync(path.join(__dirname,'refined-'+file),JSON.stringify(result)+'\n');
 console.log({size:result.size,checked:result.checked,surviving:result.surviving.length});
}
module.exports={check,choices};
