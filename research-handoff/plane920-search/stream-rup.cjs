const fs=require('node:fs'),readline=require('node:readline'),crypto=require('node:crypto'),assert=require('node:assert/strict');
async function checkProof(dimacs,proofPath){
 const lines=dimacs.trimEnd().split('\n'),header=lines.shift().split(' ');
 assert.equal(header[1],'cnf');const n=Number(header[2]),m=Number(header[3]);assert.equal(lines.length,m);
 const db=[null];
 for(const l of lines){const nums=l.trimEnd().split(' ').map(Number);assert.equal(nums.pop(),0);db.push(Int32Array.from(nums));}
 const assigned=new Int32Array(n+1),input=fs.createReadStream(proofPath),hash=crypto.createHash('sha256');
 input.on('data',chunk=>hash.update(chunk));let add=0,deleted=0,empty=false;
 for await(const line of readline.createInterface({input,crlfDelay:Infinity})){
   if(!line)continue;
   const toks=line.split(' '),id=Number(toks[0]);
   if(toks[1]==='d'){for(let i=2;i<toks.length-1;i++)delete db[Number(toks[i])];deleted++;continue;}
   add++;let conflict=false;const end=toks.indexOf('0',1);
   assert(end>=1);assert.equal(toks.at(-1),'0');assert(!db[id]);
   const newClause=new Int32Array(end-1);
   for(let j=1;j<end;j++){
     const lit=Number(toks[j]);assert(lit!==0&&Math.abs(lit)<=n);
     newClause[j-1]=lit;
     const raw=Math.abs(lit),sign=lit>0?-add:add;
     if(assigned[raw]===-sign)conflict=true;assigned[raw]=sign;
   }
   for(let j=end+1;j<toks.length-1&&!conflict;j++){
     const hint=Number(toks[j]);assert(hint>0,'RAT hint in case '+id);
     const clause=db[hint];assert(clause,'missing clause '+hint+' at '+id);let unit=0;
     for(const lit of clause){
       const val=assigned[Math.abs(lit)];
       if(val===add||val===-add){assert((val>0)!==(lit>0),'satisfied hint '+hint+' at '+id);}
       else{assert(!unit,'non-unit hint '+hint+' at '+id);unit=lit;}
     }
     if(unit)assigned[Math.abs(unit)]=unit>0?add:-add;
     else conflict=true;
   }
   assert(conflict,'missing RUP contradiction at '+id);
   db[id]=newClause;if(!newClause.length)empty=true;
 }
 assert(empty,'missing empty clause');return {add,deleted,proofSha256:hash.digest('hex'),empty};
}
module.exports={checkProof};
