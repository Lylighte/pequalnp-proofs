'use strict';
const pc=new Uint8Array(8192);for(let i=1;i<8192;i++)pc[i]=pc[i&(i-1)]+1;
const lines=Array.from({length:13},(_,i)=>[0,1,3,9].reduce((s,v)=>s|1<<((v+i)%13),0));
const rawSources=lines.map((_,i)=>lines.reduce((m,l,k)=>m|((l>>i&1)<<k),0));
function cnfFor(ah,bh,rows,required=8191){
  const high=[ah,bh],pos=new Map(lines.map((t,i)=>[t,i])),at=new Map(rows.map((t,i)=>[t,i]));
  let nv=0;const clauses=[],ports=[],dec=[];
  const fresh=()=>++nv,neg=x=>typeof x==='boolean'?!x:-x;
  function add(...ls){if(!ls.includes(true))clauses.push(ls.filter(l=>l!==false));}
  const val=rows.map(r=>lines.map((_,i)=>Boolean(r&(1<<i))));
  for(let h=0;h<6;h++){
    const sel=[0,1].map(()=>Array.from({length:13+h},fresh));ports.push(sel);
    let equal=true;
    for(let j=0;j<13+h;j++){
      const a=sel[0][j],b=sel[1][j],next=fresh();
      add(neg(equal),-a,b);add(neg(equal),a,b,next);add(neg(equal),-a,-b,next);equal=next;
    }
    for(let i=0;i<rows.length;i++){
      const r=rows[i],w=val[i];
      const sides=sel.map(side=>{
        const atoms=[];for(let j=0;j<13+h;j++){
          if(w[j]===false)continue;
          if(w[j]===true){atoms.push(side[j]);continue;}
          const both=fresh();add(-both,side[j]);add(-both,w[j]);add(both,-side[j],-w[j]);atoms.push(both);
        }
        const z=fresh();for(const a of atoms)add(-a,z);add(-z,...atoms);return z;
      });
      let g;
      if(h>=4 && pc[r]<=3)g=false;
      else if(h>=4 && pos.has(r))g=Boolean(high[h-4]&(1<<pos.get(r)));
      else g=fresh();
      add(neg(g),sides[0]);add(neg(g),sides[1]);add(g,-sides[0],-sides[1]);w.push(g);
    }
  }
  // For any triple of named lines at most one of the six helpers is absent from
  // them all. For a pair at most two are absent; a single line needs at least two.
  for(let t=1;t<8192;t++)if(pc[t]<=3&&(t&required)===t){
    const needed=[0,2,4,5][pc[t]],ss=lines.map((_,i)=>i).filter(i=>t&(1<<i));
    for(let h=1;h<64;h++)if(pc[h]===7-needed){
      const bits=[];for(let j=0;j<6;j++)if(h&(1<<j))for(const i of ss)bits.push(val[at.get(lines[i])][13+j]);
      add(...bits);
    }
  }
  const own=[[],[],[],[]];
  for(let l=0;l<13;l++){
    if(!(required&(1<<l)))continue;
    const choices=[];
    function option(lo,hi,extra){
      const yes=fresh();choices.push({yes,lo,hi});
      for(let i=0;i<rows.length;i++){
        const r=rows[i],a=val[i][lo],b=val[i][hi];
        if(r===lines[l]){add(-yes,a);add(-yes,b);}else add(-yes,neg(a),neg(b));
        if(extra!==undefined&&pc[r]<=3)add(-yes,r===extra?b:neg(b));
      }
      return yes;
    }
    if((ah&bh)===(1<<l))option(17,18);
    for(let p=0;p<13;p++)if(lines[l]&(1<<p)){
      for(let h=1;h<4;h++)own[h].push([l,option(p,13+h,lines[l]^(1<<p))]);
      for(let h=4;h<6;h++)if((rawSources[p]&high[h-4])===(1<<l))option(p,13+h);
    }
    add(...choices.map(c=>c.yes));dec.push(choices);
  }
  for(const opts of own)for(let i=0;i<opts.length;i++)for(let j=0;j<i;j++)
    if(opts[i][0]!==opts[j][0])add(-opts[i][1],-opts[j][1]);
  const cnf='p cnf '+nv+' '+clauses.length+'\n'+clauses.map(c=>c.join(' ')+' 0').join('\n')+'\n';
  return {cnf,ports,dec};
}
module.exports={cnfFor,lines,pc};

