'use strict';
const fs=require('node:fs'),path=require('node:path'),zlib=require('node:zlib'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const {check}=require('./full-private.cjs'),{signature}=require('./five-private.cjs'),{terminalGame}=require('./late-game.cjs');
const source=zlib.gunzipSync(fs.readFileSync(path.join(__dirname,'../plane920-search/branch-game-four-orbits.gz')));
assert.equal(crypto.createHash('sha256').update(source).digest('hex'),'3a6d9ef8b36ea45106becd8e592a4590fdd868cf3621e8113aa4e51fab75958e');
const dir=path.join(__dirname,'unrestricted');fs.mkdirSync(dir,{recursive:true});
const raw=Array.from({length:13},(_,i)=>[1<<i]);
const minima=ts=>[...new Set(ts)].sort((a,b)=>a-b).filter((m,i,v)=>!v.slice(0,i).some(n=>(m&n)===n));
const prod=(a,b)=>minima(a.flatMap(x=>b.map(y=>x|y)));
const join=(a,b)=>minima([...a,...b]);
function arm(p,mask,prev){
  let t=p<0?[0]:raw[p];
  for(let i=0;i<prev.length;i++)if(mask&(1<<i))t=prod(t,prev[i]);
  return t;
}
function getArms(prev){
  const store=new Map();
  for(let p=-1;p<13;p++)for(let j=0;j<(1<<prev.length);j++){
    if(p<0&&!j)continue;
    const a=arm(p,j,prev),must=a.reduce((m,v)=>m&v,8191);if(must&(must-1))continue;
    store.set(a.join(','),a);
  }
  return [...store.values()];
}
function record(id){
  const gates=[],pairs=[];
  const rec=source.subarray(id*8,id*8+8);
  for(let i=0;i<4;i++){
    const pair=[rec[2*i],rec[2*i+1]].map(v=>arm((v>>3)-1,v&7,gates));
    pairs.push(pair);gates.push(join(...pair));
  }
  return {gates,pairs};
}
const keys=a=>a.join(',');
function fixed(gates,pairs){
  const known=new Set(raw.map(keys)),mandatory=new Map();
  let dominated=false;
  for(let i=0;i<pairs.length;i++){
    const [a,b]=pairs[i].map(signature);
    if(!(a.active&~b.active)||!(b.active&~a.active))dominated=true;
    for(const t of [a,b])if(!known.has(t.key))mandatory.set(t.key,t.active);
    known.add(keys(gates[i]));
  }
  const priv=Array(13).fill(0);let shared=0;
  for(const mask of mandatory.values()){
    if(mask && !(mask&(mask-1)))priv[31-Math.clz32(mask)]++;
    else shared++;
  }
  return {dominated,priv,shared};
}
function can(gates,pairs,active,total){
  const f=fixed(gates,pairs);if(f.dominated)return [];
  const os=gates.map(signature),cost=check(os,0,0,true);
  return active.filter(h=>terminalGame(os,cost,total-13-h,h-gates.length,f.shared,f.priv));
}
function next(gates,pairs,callback){
  const list=getArms(gates),names=new Set(gates.map(keys)),sig=list.map(signature);
  for(let i=0;i<list.length;i++)for(let j=0;j<i;j++){
    const a=list[i],b=list[j],sa=sig[i].active,sb=sig[j].active;
    if(!(sa&~sb)||!(sb&~sa))continue;
    const g=join(a,b),key=keys(g);
    if(names.has(key)||key===sig[i].key||key===sig[j].key)continue;
    callback([...gates,g],[...pairs,[a,b]],i,j);
  }
}
if(require.main===module){
const from=Number(process.argv[2]||0),end=Number(process.argv[3]||1217),total=Number(process.argv[4]||27);
const initial=(process.argv[5]||'5,6,7').split(',').map(Number),log=path.join(dir,'round-'+[total,initial.join(''),from,end].join('-')+'.jsonl');
const done=new Set((fs.existsSync(log)?fs.readFileSync(log,'utf8'):'').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s).id));
for(let id=from;id<end;id++){
  if(done.has(id))continue;
  const {gates,pairs}=record(id),active=can(gates,pairs,initial,total),live=[],counts={};
  let fifth=0;
  if(active.length)next(gates,pairs,(gs,ps,i,j)=>{
    fifth++;const remain=can(gs,ps,active,total);
    if(remain.length){live.push([i,j,remain]);for(const h of remain)counts[h]=(counts[h]||0)+1;}
  });
  fs.appendFileSync(log,JSON.stringify({id,active,fifth,counts,live})+'\n');
}
console.log(JSON.stringify({from,end,total,initial,complete:true}));
}
module.exports={record,next,can,keys,join,signature,getArms,fixed};

