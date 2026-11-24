const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),crypto=require('node:crypto');
function check(cnfFile,proofFile){
 const read=f=>fs.readFileSync(path.join(__dirname,f),'utf8'),cnf=read(cnfFile),proof=read(proofFile);
 const lines=cnf.trim().split(/\r?\n/),[_,type,v,c]=lines.shift().split(/\s+/);
 assert.equal(type,'cnf');assert.equal(lines.length,Number(c));
 const db=[null,...lines.map(l=>l.split(/\s+/).map(Number).slice(0,-1))];
 const marks=new Int32Array(Number(v)+1);let stamp=0,adds=0,dels=0,empty=false;
 function value(lit){const x=marks[Math.abs(lit)];return Math.abs(x)===stamp?Math.sign(x)*Math.sign(lit):0;}
 function assign(lit){marks[Math.abs(lit)]=Math.sign(lit)*stamp;}
 for(const line of proof.trim().split(/\r?\n/)){
   const tokens=line.split(/\s+/),id=Number(tokens[0]);
   if(tokens[1]==='d'){
     assert.equal(tokens.at(-1),'0');
     for(const tok of tokens.slice(2,-1))db[Number(tok)]=null;
     dels++;continue;
   }
   stamp++;const nums=tokens.map(Number),sep=nums.indexOf(0,1);assert(sep>0);assert.equal(nums.at(-1),0);
   const pending=nums.slice(1,sep);assert(!db[id]);
   let conflict=false;for(const lit of pending){if(value(-lit)<0)conflict=true;assign(-lit);}
   for(let j=sep+1;j<nums.length-1&&!conflict;j++){
     const h=nums[j];assert(h>0,'RAT hints unsupported');const ref=db[h];assert(ref,'missing clause '+h);
     let open=0,count=0;
     for(const lit of ref){const e=value(lit);assert(e!==1,'hint is satisfied at '+id);if(e===0){count++;open=lit;}}
     assert(count<=1,'hint is not unit at '+id);if(count)assign(open);else conflict=true;
   }
   assert(conflict,'no conflict at '+id);db[id]=pending;adds++;if(!pending.length)empty=true;
 }
 assert(empty,'missing empty clause');
 const sha=s=>crypto.createHash('sha256').update(s).digest('hex');
 return {cnfFile,proofFile,vars:Number(v),clauses:Number(c),adds,dels,empty,cnfSha256:sha(cnf),proofSha256:sha(proof)};
}
module.exports={check};
if(require.main===module)console.log(JSON.stringify(check(process.argv[2],process.argv[3])));
