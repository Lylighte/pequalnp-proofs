const fs=require('node:fs'),path=require('node:path'),zlib=require('node:zlib'),assert=require('node:assert/strict');
const {lines}=require('./branch-game.json'),forest=require('../plane920-core/or-forest-five.json'),earlier=require('./surplus-and-shapes.json').live;
const size=Array.from({length:8192},(_,i)=>i.toString(2).replaceAll('0','').length),domain=Array.from({length:8192},(_,m)=>m).filter(m=>size[m]<=4);
const full=(1n<<BigInt(domain.length))-1n;
const raw=Array.from({length:13},(_,i)=>({terms:[1<<i],w:domain.reduce((s,m,j)=>s|((m&1<<i)?1n<<BigInt(j):0n),0n)}));
const pos=m=>lines.reduce((s,L,i)=>s|(m.some(x=>(x&L)===x)?1<<i:0),0);
const positive=raw.map(a=>pos(a.terms));
const core=Array.from({length:8192},(_,m)=>lines.reduce((p,L,i)=>(m&1<<i)?p&L:p,8191));
const allMasks=Array.from({length:32},(_,m)=>m).filter(m=>size[m]>=2);
function prime(ts){const v=[...new Set(ts)].sort((a,b)=>a-b);return v.filter((m,i)=>!v.slice(0,i).some(q=>(q&m)===q));}
function arm(p,J,ors){
 let v=p<0?[0]:[1<<p],w=p<0?full:raw[p].w;
 for(let i=0;i<ors.length;i++)if(J&1<<i){v=prime(v.flatMap(m=>ors[i].terms.map(t=>t|m)));w&=ors[i].w;}
 return {terms:v,w,p,J};
}
const joined=(a,b)=>({terms:prime([...a.terms,...b.terms]),w:a.w|b.w});
const implied=(a,ors)=>ors.reduce((m,x,i)=>m|((!((~x.w)&a.w))?1<<i:0),0);
const scope=a=>a.terms.reduce((v,x)=>v|x,0);
const resource=(a,ors)=>({v:pos(a.terms),mask:implied(a,ors),w:a.w});
function runPrefix(f,processRow){
 const {record,components,orbit}=f,known=[...raw],ors=[];
 for(let j=0;j<4;j++){
   const own=record.slice(2*j,2*j+2).map(c=>arm((c>>3)-1,c%8,ors)),out=joined(...own);
   known.push(...own,out);ors.push(out);
 }
 const base=known.map(w=>resource(w,ors)),choices=new Map();
 for(let p=-1;p<13;p++)for(let J=0;J<16;J++){
   if(p<0&&!J)continue;const a=arm(p,J,ors),intersection=a.terms.reduce((v,u)=>v&u,8191);
   if(size[intersection]>1)continue;const s=scope(a);
   a.part=components.reduce((v,c)=>v|(s&c?c:0),s);
   a.key=a.terms.join(',');a.oldMask=implied(a,ors);a.v=pos(a.terms);
   choices.set(a.key,a);
 }
 const aa=[...choices.values()],oldKeys=ors.map(a=>a.terms.join(','));
 const oldPos=Array.from({length:16},(_,I)=>ors.reduce((v,u,i)=>v&((I&1<<i)?pos(u.terms):8191),8191));
 let number=0;
 for(let i=0;i<aa.length;i++)for(let j=0;j<i;j++){
   const a=aa[i],b=aa[j];if(a.part&b.part)continue;
   const e=joined(a,b),key=e.terms.join(',');if(key===a.key||key===b.key||oldKeys.includes(key))continue;
   const positive5=a.v|b.v,d=[];
   for(const item of base)d.push([item.mask|((item.w&~e.w)===0n?16:0),item.v]);
   d.push([a.oldMask|16,a.v],[b.oldMask|16,b.v],[implied(e,ors)|16,positive5]);
   const pairs=[];
   for(const I of allMasks){
     let live=oldPos[I&15]&((I&16)?positive5:8191);
     if(size[live]<4||core[live])continue;
     for(const [available,v] of d)if((available&I)===I)live&=~v;
     if(size[live]>=4&&!core[live])pairs.push([I,live]);
   }
   processRow({orbit,number,a,b,e,pairs,ors});number++;
 }
 return number;
}
if(require.main===module){
 const coverage={},maxHist={},prefixes=[],records=[];let count=0,totalI=0,anyTime=0,after=0;
 for(const f of forest.prefixes){
   const had=earlier[f.orbit].byLevel[3].length>0;let at5=0,localI=0;
   const n=runPrefix(f,({orbit,number,pairs})=>{
     if(had||pairs.length)anyTime++;
     if(!pairs.length)return;after++;at5++;localI+=pairs.length;
     const high=Math.max(...pairs.map(x=>size[x[1]]));maxHist[high]=(maxHist[high]||0)+1;
     for(const [,m] of pairs)coverage[size[m]]=(coverage[size[m]]||0)+1;
     records.push([orbit,number,pairs]);
   });
   count+=n;totalI+=localI;prefixes.push({orbit:f.orbit,completions:n,had,at5,candidates:localI});
 }
 assert.equal(count,forest.completions);
 const summary={prefixes:forest.prefixes.length,count,anyTime,after,totalI,coverage,maxHist,livePrefixes:prefixes.filter(x=>x.at5).length};
 const gzip=zlib.gzipSync(Buffer.from(JSON.stringify(records)),{level:6});
 fs.writeFileSync(path.join(__dirname,'surplus-fifth-live.json.gz'),gzip);
 fs.writeFileSync(path.join(__dirname,'surplus-fifth.json'),JSON.stringify({summary,prefixes,packedBytes:gzip.length})+'\n');
 console.log(summary);
}
module.exports={runPrefix};
