"use strict";
const fs=require("node:fs"),path=require("node:path"),assert=require("node:assert/strict");
const all=(1<<13)-1,allLines=[...Array(13)].map((_,t)=>[0,1,3,9].reduce((v,p)=>v|(1<<((p+t)%13)),0));
const dropped=Number(process.argv[4]??0),lines=allLines.filter((_,i)=>!(dropped&(1<<i)));
const weight=new Uint8Array(all+1),active=new Uint16Array(all+1);
for(let u=1;u<=all;u++){
    weight[u]=weight[u&(u-1)]+1;
    lines.forEach((l,i)=>{if(weight[l&u]>1)active[u]|=1<<i;});
}
const seven=process.argv[2]!=="control",strong=process.argv[2]==="strong",orCap=process.argv.includes("--or-cap");
const floor=[0,0,0,0,0,1,1,seven?3:2,3,4,5,6,7,8];
const localFloor=new Uint8Array(all+1);
const sixMap=new Uint8Array(all+1);
const sixSmall=JSON.parse(fs.readFileSync(path.join(__dirname,"small-core","results-6-2.json"),"utf8")).records;
for(const r of sixSmall)for(const u of r.orbit)sixMap[u]=r.verdict==="UNSAT"?3:2;
for(let u=1;u<=all;u++){
    const sizes=lines.map(l=>weight[l&u]),a=sizes.filter(k=>k===3).length,b=sizes.filter(k=>k===4).length;
    localFloor[u]=b>=2||(b===1&&a>=1)||a>=4?3:b||a>=2?2:a?1:0;
    if(allLines.every((l,i)=>!(dropped&(1<<i))||weight[l&u]<=2)){
        if(weight[u]===6)localFloor[u]=Math.max(localFloor[u],sixMap[u]);
        if(weight[u]===7)localFloor[u]=b===2?4:5;
        if(weight[u]===8)localFloor[u]=Math.max(localFloor[u],4);
        if(weight[u]===9)localFloor[u]=Math.max(localFloor[u],5);
    }
}
if(dropped){
    const dir=path.join(__dirname,"small-core","deleted");
    if(fs.existsSync(dir))for(const f of fs.readdirSync(dir)){
        const matches=f.match(/^(\d+)-(\d+)-(\d+)\.json$/);
        if(!matches||Number(matches[3])!==dropped)continue;
        for(const r of JSON.parse(fs.readFileSync(path.join(dir,f),"utf8")))if(r.verdict==="UNSAT"&&r.check.empty)
            for(const u of r.orbit)localFloor[u]=Math.max(localFloor[u],Number(matches[2])+1);
    }
}
const bounds=new Map(),states=new Map(),splits=new Map(),winners=new Map();
const nogoods=new Map(),cefile=path.join(__dirname,"small-core","deleted","nogoods-"+dropped+".json");
if(dropped&&fs.existsSync(cefile))for(const r of JSON.parse(fs.readFileSync(cefile,"utf8")))if(r.verdict==="UNSAT"&&r.check.empty)
    for(const [u,h] of r.images){if(!nogoods.has(u))nogoods.set(u,[]);nogoods.get(u).push([h,r.k+1]);}
const trans=path.join(__dirname,"small-core","deleted","transferred-"+dropped+".json");
if(dropped&&fs.existsSync(trans))for(const [u,h,lb] of JSON.parse(fs.readFileSync(trans,"utf8"))){
    if(!nogoods.has(u))nogoods.set(u,[]);nogoods.get(u).push([h,lb]);
}
function charge(region,owners){
    owners&=active[region];
    const id=region*8192+owners;
    if(bounds.has(id))return bounds.get(id);
    let cost=0;
    for(let o=owners;o;o&=o-1)cost+=weight[region&lines[Math.log2(o&-o)]]-1;
    cost=Math.max(cost,dropped?localFloor[region]:strong?Math.max(localFloor[region],floor[weight[region]]):floor[weight[region]]);
    for(const [mask,lb] of nogoods.get(region)??[])if((owners&mask)===mask)cost=Math.max(cost,lb);
    bounds.set(id,cost);return cost;
}
function partitions(u){
    if(splits.has(u))return splits.get(u);
    const list=[];
    for(let x=u&(u-1);x;x=(x-1)&u){
        const y=u^x;if(x>y)continue;
        const cut=lines.map((l,i)=>({i,lx:l&x,ly:l&y})).filter(c=>c.lx&&c.ly);
        const mask=cut.reduce((s,c)=>s|(1<<c.i),0);
        list.push({x,y,cut,mask});
    }
    splits.set(u,list);return list;
}
function fits(u,owners,remaining){
    owners&=active[u];remaining=Math.min(remaining,weight[u]-1);
    if(charge(u,owners)>remaining)return false;
    if(weight[u]===1)return true;
    const idx=(u*8192+owners)*16+remaining;
    if(states.has(idx))return states.get(idx);
    let solution=false;
    for(const {x,y,cut,mask} of partitions(u)){
        const forced=owners&mask;
        if(weight[forced]>1)continue;
        function distribute(ox,oy,available,maxX=weight[x]-1,maxY=weight[y]-1){
            available=Math.min(available,maxX+maxY);
            const lox=charge(x,ox),loy=charge(y,oy);
            if(lox+loy>available||lox>maxX||loy>maxY)return false;
            // Allocate the *right* child's exact budget, in descending order.
            for(let right=Math.min(available-lox,maxY);right>=loy;right--){
                const left=Math.min(available-right,maxX);
                if(fits(y,oy,right)&&fits(x,ox,left)){
                    winners.set(idx,{u,owners,remaining,x,ox,left,y,oy,right});
                    return true;
                }
            }
            return false;
        }
        const allX=active[x]&(mask|owners),allY=active[y]&(mask|owners);
        if(!forced&&distribute(allX,allY,remaining)){solution=true;break;}
        if(!remaining)continue;
        const fixed=forced?cut.find(c=>(1<<c.i)===forced):null;
        const labelsX=fixed?[fixed.lx]:[...new Set([0,...cut.map(c=>c.lx)])],
              labelsY=fixed?[fixed.ly]:[...new Set([0,...cut.map(c=>c.ly)])];
        for(const px of labelsX){
            for(const py of labelsY){
                if(orCap){
                    let allowX=0,allowY=0;
                    for(const {i,lx,ly} of cut)if(!(owners&(1<<i))){
                        if(ly===py&&weight[lx]>=2)allowX|=1<<i;
                        if(lx===px&&weight[ly]>=2)allowY|=1<<i;
                    }
                    for(let wa=allowX;;wa=(wa-1)&allowX){
                        const allowed=allowY&~wa;
                        for(let wb=allowed;;wb=(wb-1)&allowed){
                            if(distribute(allX&~wa,allY&~wb,remaining-1,
                                weight[x]-1-Math.max(0,weight[wa]-1),weight[y]-1-Math.max(0,weight[wb]-1))){solution=true;break;}
                            if(!wb)break;
                        }
                        if(solution||!wa)break;
                    }
                    if(solution)break;
                    continue;
                }
                let mustX=owners&active[x],mustY=owners&active[y],either=0;
                for(const {i,lx,ly} of cut){
                    const bit=1<<i;
                    if(owners&bit)continue;
                    const needX=weight[lx]>1,needY=weight[ly]>1;
                    const canSkipX=ly===py,canSkipY=lx===px;
                    if(needX&&!canSkipX)mustX|=bit;
                    if(needY&&!canSkipY)mustY|=bit;
                    if(needX&&needY&&canSkipX&&canSkipY)either|=bit;
                }
                // Covers the general disjunction as well as singleton ambiguity.
                for(let pick=either;;pick=(pick-1)&either){
                    if(distribute(mustX|pick,mustY|(either^pick),remaining-1)){solution=true;break;}
                    if(!pick)break;
                }
                if(solution)break;
            }
            if(solution)break;
        }
        if(solution)break;
    }
    states.set(idx,solution);return solution;
}
const geometry={};
for(let u=1;u<=all;u++)if(weight[u]===7){
    const intersections=allLines.map(l=>weight[l&u]),n3=intersections.filter(v=>v===3).length,n4=intersections.filter(v=>v===4).length;
    assert(n4>=2||(n4===1&&n3>=1)||(!n4&&n3>=5));
    const k=n3+","+n4;geometry[k]=(geometry[k]??0)+1;
}
const limit=Number(process.argv[3]??8);
const full=fits(all,0,limit),result={seven,strong,orCap,dropped,limit,full,states:states.size,geometry};
if(full){
    result.witness=[];
    function collect(u,h,c){
        const q=winners.get((u*8192+(h&active[u]))*16+Math.min(c,weight[u]-1));
        if(!q)return;
        result.witness.push(q);collect(q.x,q.ox,q.left);collect(q.y,q.oy,q.right);
    }
    collect(all,0,limit);
}
fs.writeFileSync(path.join(__dirname,"audit-obligations-"+(strong?"strong":Number(seven))+"-"+limit+(dropped?"-drop"+dropped:"")+(orCap?"-orcap":"")+".json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify(result));
