const fs=require('node:fs'),path=require('node:path');
const {table,mult,join,raw,loc,lines,univ,pm,pc}=require('./three-or-five-lines.cjs');
const rawTerms=raw.map((_,p)=>[1<<p]);
function armOptions(prefix,rawSets=rawTerms){
  const all=new Map();
  const choices=[null,...rawSets];
  for(const rawPart of choices)for(let subset=0;subset<1<<prefix.length;subset++){
    if(!rawPart&&!subset)continue;
    let v=rawPart||[0];for(let j=0;j<prefix.length;j++)if(subset&1<<j)v=mult(v,prefix[j]);
    all.set(v.join(','),v);
  }
  return [...all.values()];
}
function decompositions(terms){
  const out=[],seen=new Set();
  function visit(i,paid){
    if(i===terms.length){const k=paid.map(x=>x.join(',')).sort().join('/');if(!seen.has(k)){seen.add(k);out.push(paid);}return;}
    const key=terms[i].join(','),prev=terms.slice(0,i),options=armOptions(prev);
    const atoms=new Set([...rawTerms,...prev].map(t=>t.join(',')));
    for(let u=0;u<options.length;u++)for(let v=0;v<u;v++){
      const a=options[u],b=options[v];if(join(a,b).join(',')!==key)continue;
      const copy=[...paid],used=new Set(paid.map(q=>q.join(',')));
      for(const x of [a,b]){const s=x.join(',');if(!atoms.has(s)&&!used.has(s)){used.add(s);copy.push(x);}}
      visit(i+1,copy);
    }
  }
  visit(0,[]);return out;
}
function priced(terms,paid,n,budget,targetFamily=0,maxPrivate=100,disjointCuts=[]){
  return pricedTables(terms.map(table),paid.map(table),n,budget,targetFamily,maxPrivate,disjointCuts);
}
function pricedTables(flags,fixed,n,budget,targetFamily=0,maxPrivate=100,disjointCuts=[],strongCuts=false){
  const pos=fixed.map(pm),groups=new Map(),all=[univ];
  for(const w of flags)for(const z of [...all])all.push(z&w);
  for(const atom of [univ,...raw])for(const z of all){const w=atom&z,m=pm(w);if(pc[m]>=2)groups.set(m,(groups.get(m)??univ)&w);}
  const free=new Set([...raw,...flags,...fixed,univ]);
  for(const m of pos)if(groups.has(m))free.add(groups.get(m));
  const opt=[...groups].filter(([m,w])=>!free.has(w));
  const choices=loc.map((at,i)=>{
    const opts=[];for(const w of free)if(w&at)opts.push([w^at,0n]);
    opt.forEach(([m,w],j)=>{if(w&at)opts.push([w^at,1n<<BigInt(j)]);});
    const two=new Set(),three=new Set();
    for(let a=0;a<opts.length;a++)for(let b=0;b<=a;b++){
      const [aw,atags]=opts[a],[bw,btags]=opts[b],uv=aw&bw,both=atags|btags;
      if(!uv){two.add(both);continue;}
      for(let c=0;c<b;c++)if(!(uv&opts[c][0]))three.add(both|opts[c][1]);
    }
    const reduce=vs=>[...vs].filter(v=>![...vs].some(k=>k!==v&&(v&k)===k));
    return [reduce(two),reduce(new Set([...two,...three]))];
  });
  const price=tags=>choices.map(([x,y])=>x.some(t=>(t&tags)===t)?0:y.some(t=>(t&tags)===t)?1:2);
  const cheapest=price((1n<<BigInt(opt.length))-1n);
  const min=cheapest.filter((_,i)=>!targetFamily||(targetFamily&1<<i)).sort((a,b)=>a-b).slice(0,n).reduce((a,b)=>a+b);
  const families=[];for(let family=0;family<8192;family++)if(pc[family]===n&&(!targetFamily||family===targetFamily)&&disjointCuts.every(m=>m&family)&&cheapest.every((c,j)=>!(family&1<<j)||c+pos.filter(m=>(m&family)===(1<<j)).length<=maxPrivate))families.push(family);
  if(!families.length)return {found:null,tried:0};
  const bound=new Uint8Array(8192);for(let sub=1;sub<8192;sub++){const k=pc[sub];if(k>n)continue;bound[sub]=[0,2,4,5][Math.min(k,3)];if(strongCuts){let e=0;for(let j=0;j<disjointCuts.length;j+=2)if((sub&disjointCuts[j])&&(sub&disjointCuts[j+1]))e++;if(k>=5)bound[sub]=6;if(e<=4&&k>=5)bound[sub]=k===5?8:9;if(e<=3&&k>=3)bound[sub]=2*Math.min(k,6)-1;if(e<=1)bound[sub]=2*k;}}
  let found=null,tried=0;
  function scan(i,r,chosen,tags){
    if(r){for(let j=i;j+r<=opt.length&&!found;j++)scan(j+1,r-1,[...chosen,j],tags|1n<<BigInt(j));return;}
    tried++;const costs=price(tags),active=[...pos,...chosen.map(i=>opt[i][0])],avail=budget-active.length;
    for(const family of families){
      if(disjointCuts.some(m=>!(m&family)))continue;
      let sum=0;for(let j=0;j<13;j++)if(family&1<<j){if(costs[j]+active.filter(m=>(m&family)===(1<<j)).length>maxPrivate){sum=budget+1;break;}sum+=costs[j];}if(sum>avail)continue;
      let sound=true;for(let sub=family;sub;sub=(sub-1)&family){
        const k=pc[sub];if(k>3&&!strongCuts)continue;
        let left=budget-active.filter(z=>!(z&sub)).length;
        for(let j=0;j<13;j++)if((family^sub)&1<<j)left-=costs[j];
        if(left<bound[sub]){sound=false;break;}
      }
      if(sound){found={family,costs,active,chosen};break;}
    }
  }
  for(let s=0;s<=budget-fixed.length-min&&!found;s++)scan(0,s,[],0n);
  return {found,tried};
}
if(require.main===module){
 const k=Number(process.argv[2]||4),budget=Number(process.argv[3]||6);
 const source=JSON.parse(fs.readFileSync(path.join(__dirname,'few-or-3-'+k+'-'+budget+'.json'))).live,report=[];
 for(const {terms} of source){
   const rows=decompositions(terms).map(paid=>({paid,...priced(terms,paid,k,budget)}));
   report.push({terms,rows});
 }
 fs.writeFileSync(path.join(__dirname,k===4&&budget===6?'paid-or-three-four-six.json':'paid-three-'+k+'-'+budget+'.json'),JSON.stringify(report)+'\n');
 console.log(report.map(({rows})=>({decompositions:rows.length,survivors:rows.filter(x=>x.found).length})));
}
module.exports={decompositions,armOptions,priced,pricedTables};
