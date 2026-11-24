'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((m,d)=>m+2**((d+i)%13),0));
const bits=new Uint8Array(8192), costs=new Uint8Array(8192);
for(let i=1;i<8192;i++)bits[i]=bits[i>>>1]+(i&1);
const minimum=[0,0,0];
for(let n=3;n<=13;n++){
 let min=99;
 for(let U=1;U<8192;U++)if(bits[U]===n){
   let m=99;
   for(let X=(U-1)&U;X;X=(X-1)&U){
     const Y=U^X;
     if(X<Y)continue;
     const down=costs[X]+costs[Y];if(down>=m)continue;
     const left=new Map([[0,0]]),right=new Map([[0,0]]),pair=new Map();
     let total=0;
     for(const L of lines){
       const a=L&X,b=L&Y;if(!a||!b)continue;
       let u=bits[a]-1,v=bits[b]-1;total+=u+v;
       left.set(a,(left.get(a)||0)+v);right.set(b,(right.get(b)||0)+u);
       pair.set(a*8192+b,(pair.get(a*8192+b)||0)+Math.min(u,v));
     }
     let maxDiscount=0;
     for(const [a,wa] of left)for(const [b,wb] of right)maxDiscount=Math.max(maxDiscount,wa+wb-(pair.get(8192*a+b)||0));
     const noSwitch=Math.max(down+1,total+1-maxDiscount);
     const switched=Math.max(down,total);
     m=Math.min(m,noSwitch,switched);
   }
   costs[U]=m;min=Math.min(min,m);
 }
 minimum.push(min);
}
const expected=JSON.parse(fs.readFileSync(path.join(__dirname,'merge-all-slices.json'),'utf8'));
for(let n=3;n<=13;n++){
 const hist={};
 for(let U=0;U<8192;U++)if(bits[U]===n)hist[costs[U]]=(hist[costs[U]]||0)+1;
 assert.deepEqual(hist,expected.bySize[n]);
}
console.log(JSON.stringify({full:costs[8191],minimumBySize:minimum,matchingHistograms:11}));
