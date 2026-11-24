const fs=require('node:fs'),path=require('node:path'),zlib=require('node:zlib'),assert=require('node:assert/strict');
const {lines}=require('./branch-game.json'),full=8191;
const size=Array.from({length:8192},(_,i)=>i.toString(2).replaceAll('0','').length);
const ids=Array.from({length:8192},(_,i)=>i).filter(i=>size[i]<=4);
assert.equal(ids.length,1093);
const bits=Array.from({length:13},(_,i)=>ids.reduce((s,m,j)=>m&1<<i?s|1n<<BigInt(j):s,0n));
const all=(1n<<BigInt(ids.length))-1n,rows=lines.map(m=>1n<<BigInt(ids.indexOf(m)));
const unpack=s=>rows.reduce((m,b,i)=>m|((s&b)?1<<i:0),0);
const core=m=>lines.reduce((p,L,i)=>(m&1<<i)?p&L:p,full);
const ref=require('./branch-game-four-replay.json'),records=zlib.gunzipSync(fs.readFileSync(path.join(__dirname,'branch-game-four-orbits.gz')));
assert.equal(records.length,ref.syntacticOrbits*8);
function possibilities(previous,known){
 const r=previous.length,ret=[];
 for(let I=1;I<(1<<r);I++)if(size[I]>=2){
   const E=previous.reduce((v,w,i)=>v&((I&1<<i)?w:all),all);
   const removed=known.reduce((v,w)=>v|((w&~E)===0n?w:0n),0n);
   const potential=unpack(E&~removed);
   if(size[potential]>=4&&!core(potential))ret.push({I,potential});
 }
 return ret;
}
const live=[],hist={},byPrefix={};
for(let i=0;i<records.length;i+=8){
 const rec=Array.from(records.subarray(i,i+8)),known=[...bits],ors=[],byLevel=[];
 for(let j=0;j<4;j++){
   const own=rec.slice(2*j,2*j+2).map(byte=>{
     const p=(byte>>3)-1,mask=byte%8;
     return ors.reduce((v,w,k)=>v&((mask&1<<k)?w:all),p<0?all:bits[p]);
   });
   const out=own[0]|own[1];known.push(...own,out);ors.push(out);
   byLevel.push(possibilities(ors,known));
 }
 const code=byLevel.map(a=>Number(a.length>0)).join('');
 byPrefix[code]=(byPrefix[code]||0)+1;
 for(let j=0;j<4;j++)for(const {potential} of byLevel[j]){
   const label=[j+1,size[potential]].join(':');hist[label]=(hist[label]||0)+1;
 }
 live.push({id:i/8,rec,byLevel});
}
const summary={cases:live.length,byPrefix,hist,activeAt:[0,1,2,3].map(j=>live.filter(x=>x.byLevel[j].length).length)};
fs.writeFileSync(path.join(__dirname,'surplus-and-shapes.json'),JSON.stringify({summary,live})+'\n');
console.log(summary);
