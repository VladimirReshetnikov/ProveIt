
function gather(core,lines,sites,ins,seedSteps,K=6) {
const rows=core.rowsOf(lines),cs=core.contracts(sites,ins),patterns={},boxes=new Set([0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198]),pcache=new Map();
function prefix(s,k){
if(!k)return[0];if(!s.length)return[0];let key=k+":"+JSON.stringify(s);if(pcache.has(key))return pcache.get(key);
let x=s[0],tail=s.slice(1),ans;
if(x[0]==="b")ans=prefix(tail,k-1).map(p=>x[1]|(p<<1));
else if(x[0]==="x")ans=Array.from({length:1<<k},(_,i)=>i);
else if(x[0]==="r"){let[,b,a,d]=x,out=new Set();for(let n=0;n<=k;n++){let len=a*n+d;if(len>=k){out.add(b?(1<<k)-1:0);break;}let first=b?(1<<len)-1:0;for(const p of prefix(tail,k-len))out.add(first|(p<<len));if(a===0)break;}ans=Array.from(out);}
else throw Error("seg");
if(pcache.size>5000)pcache.clear();pcache.set(key,ans);return ans;
}
function rev(x,n){let y=0;for(let i=0;i<n;i++){y=(y<<1)|(x&1);x>>=1;}return y;}
const seen=new Set();
function obs(s){let[q,onl,l,r]=s;if(boxes.has(q))return;let key=JSON.stringify(s);if(seen.has(key))return;seen.add(key);let lp=prefix(l,onl?K+1:K),rp=prefix(r,onl?K:K+1),out=patterns[q]??=new Set();for(const a of lp)for(const b of rp)out.add(onl?(rev(a,K+1)|(b<<(K+1))):(rev(a,K)|(b<<K)));}
let total=0,max=0;
for(let ci=0;ci<cs.length;ci++){let c=cs[ci],[site,br,s,t]=c,moved=false;for(let k=0;k<1024;k++){if(moved&&(t===null?s[0]===254:core.matches(s,t))){total+=k;max=Math.max(max,k);break;}obs(s);let nxt=core.step(rows,br,s);if(!nxt)throw Error("fail"+ci);s=nxt[0];moved||=nxt[1];if(k===1023)throw Error("fuel");}}
const ones=new Set();let q=74,h=0;for(let i=0;i<seedSteps;i++){if(!boxes.has(q)){let p=0;for(let j=-K;j<=K;j++)if(ones.has(h+j))p|=1<<(j+K);(patterns[q]??=new Set()).add(p);}let[w,d,n]=rows[q*2+(ones.has(h)?1:0)];if(w)ones.add(h);else ones.delete(h);q=n;h+=d?1:-1;}
const result=Object.fromEntries(Object.entries(patterns).map(([q,s])=>[q,Array.from(s)]));
return {patterns:result,stats:{cases:cs.length,total,max,observed:seen.size,states:Object.keys(result).length,patterns:Object.values(result).reduce((s,a)=>s+a.length,0),seedFinal:[q,h]}};
}

function searchLocal(lines,patterns,K=6,STEP=120,detail=false){
const labels=Array.from(new Set(lines.map(x=>x[0]))).sort((a,b)=>a-b),index=Object.fromEntries(labels.map((x,i)=>[x,i])),n=labels.length,tab=Array.from({length:n},()=>[]);
for(const[q,b,w,d,t]of lines)tab[index[q]][b]=[w,d?1:-1,index[t]===undefined?n:index[t]];
const pats=labels.map(q=>patterns[q]||[]);
const acts=[];for(let t=0;t<=n;t++)for(let w=0;w<2;w++)for(let d of[-1,1])acts.push([w,d,t]);
const sol=tab.map(()=>[{},{}]);
for(let q=0;q<n;q++){if(!patterns[labels[q]])continue;for(let b=0;b<2;b++){
const ps=pats[q].filter(p=>((p>>K)&1)===b),[w,d,tgt]=tab[q][b];
for(let ai=0;ai<acts.length;ai++){let[firstw,firstd,firstn]=acts[ai],ok=true,vis=new Set(),max=0;
for(const p of ps){let tp=(p&~(1<<K))|(w<<K),h=firstd,t=(p&~(1<<K))|(firstw<<K),c=firstn,hit=false;
for(let st=1;st<=STEP;st++){if(c===tgt&&h===d&&t===tp){hit=true;max=Math.max(max,st);break;}if(c===q||c>=n||h< -K||h>K)break;vis.add(c);let op=tab[c][(t>>(h+K))&1];t=(t&~(1<<(h+K)))|(op[0]<<(h+K));h+=op[1];c=op[2];}
if(!hit){ok=false;break;}}
if(ok)sol[q][b][ai]={vis:Array.from(vis),max};
}}}
let found=[];
for(let a=0;a<n;a++)for(let r=a+1;r<n;r++){if(!patterns[labels[a]]||!patterns[labels[r]])continue;let opts=[0,1].map(b=>Object.keys(sol[a][b]).filter(ai=>sol[r][b][ai]&&!sol[a][b][ai].vis.includes(r)&&!sol[r][b][ai].vis.includes(a)).map(ai=>acts[ai].map((v,k)=>k===2?(labels[v]===undefined?254:labels[v]):v)));if(opts.every(x=>x.length))found.push({a:labels[a],r:labels[r],opts});}
const dirs=tab.map(()=>new Set());for(let q=0;q<n;q++)for(let b=0;b<2;b++){let a=tab[q][b];if(a[2]<n)dirs[a[2]].add(a[1]);}
let offsets=[];
for(let a=0;a<n;a++){if(labels[a]===74||!patterns[labels[a]]||dirs[a].size!==1)continue;let shift=-2*Array.from(dirs[a])[0];
for(let r=0;r<n;r++){if(a===r)continue;let ok=true,longest=0;
for(const p of pats[a]){let bit=(p>>K)&1,[w,d,tgt]=tab[a][bit],target=tgt===a?r:tgt,th=d+(tgt===a?shift:0),tp=(p&~(1<<K))|(w<<K);let q=r,h=shift,t=p,hit=false;
for(let st=0;st<=STEP;st++){if(st&&q===target&&h===th&&t===tp){hit=true;longest=Math.max(st,longest);break;}if(h < -K||h>K||q>=n||q===a)break;let act=tab[q][(t>>(h+K))&1];t=(t&~(1<<(h+K)))|(act[0]<<(h+K));h+=act[1];q=act[2];if(q===a){q=r;h+=shift;}}
if(!hit){ok=false;break;}}
if(ok)offsets.push({a:labels[a],r:labels[r],shift,longest,contexts:pats[a].length});}}
return {found,offsets,states:n,window:K,stepBound:STEP,...(detail?{sol,labels,acts}:{})};
}
function bypass(lines,patterns,K=6,STEP=120) {
const labels=Array.from(new Set(lines.map(x=>x[0]))).sort((a,b)=>a-b),index=Object.fromEntries(labels.map((x,i)=>[x,i])),n=labels.length,tab=Array.from({length:n},()=>[]);
for(const[q,b,w,d,t]of lines)tab[index[q]][b]=[w,d?1:-1,index[t]===undefined?n:index[t]];
const pats=labels.map(q=>patterns[q]||[]);
const inc=tab.map(()=>[]);for(let q=0;q<n;q++)for(let b=0;b<2;b++)if(tab[q][b][2]<n)inc[tab[q][b][2]].push([q,b]);
const acts=[];for(let t=0;t<n;t++)for(let w=0;w<2;w++)for(let d of[-1,1])acts.push([w,d,t]);
let found=[],tested=0;
for(let a=0;a<n;a++){
 if(labels[a]===74||inc[a].some(([q,b])=>q===a||!patterns[labels[q]]))continue;
 const incoming=inc[a],changed=new Set(incoming.map(([q,b])=>q*2+b)),rowChoices=[];
 let worked=true;tested++;
 for(let [q,b]of incoming){
  const req=pats[q].filter(p=>((p>>K)&1)===b).map(p=>{
   let[w,d,tgt]=tab[q][b],tp=(p&~(1<<K))|(w<<K),h=d;
   let op=tab[a][(tp>>(h+K))&1];tp=(tp&~(1<<(h+K)))|(op[0]<<(h+K));h+=op[1];
   return {p,t:tp,h,q:op[2]};
  }),opts=[];
  for(let ai=0;ai<acts.length;ai++){
   const[fw,fd,fn]=acts[ai];if(fn===a)continue;let ok=true,longest=0;
   for(const r of req){let c=fn,h=fd,t=(r.p&~(1<<K))|(fw<<K),hit=false;
    for(let st=1;st<=STEP;st++){
     if(c===r.q&&h===r.h&&t===r.t){hit=true;longest=Math.max(longest,st);break;}
     if(c>=n||c===a||h< -K||h>K)break;let bit=(t>>(h+K))&1;
     if(changed.has(c*2+bit))break;
     let op=tab[c][bit];t=(t&~(1<<(h+K)))|(op[0]<<(h+K));h+=op[1];c=op[2];
    }if(!hit){ok=false;break;}
   }if(ok)opts.push({action:[fw,fd,labels[fn]],longest});
  }
  if(!opts.length){worked=false;break;}rowChoices.push({q:labels[q],b,opts});
 }
 if(worked)found.push({a:labels[a],incoming:rowChoices});
}
return{found,tested,window:K,stepBound:STEP};
}

function directSearch(lines,patterns,K=6,STEP=120) {
const labels=Array.from(new Set(lines.map(x=>x[0]))).sort((a,b)=>a-b),index=Object.fromEntries(labels.map((x,i)=>[x,i])),n=labels.length,tab=Array.from({length:n},()=>[]);
for(const[q,b,w,d,t]of lines)tab[index[q]][b]=[w,d?1:-1,index[t]===undefined?n:index[t]];
let out=[];
for(let a=0;a<n;a++){let ps=patterns[labels[a]];if(!ps||labels[a]===74)continue;for(let r=0;r<n;r++){if(a===r)continue;let ok=true,longest=0;
for(let p of ps){let [w,d,tgt]=tab[a][(p>>K)&1],target=tgt===a?r:tgt,tp=(p&~(1<<K))|(w<<K),c=r,h=0,t=p,hit=false;
for(let st=0;st<=STEP;st++){if(st&&c===target&&h===d&&t===tp){hit=true;longest=Math.max(longest,st);break;}if(c>=n||h< -K||h>K)break;let op=tab[c][(t>>(h+K))&1];t=(t&~(1<<(h+K)))|(op[0]<<(h+K));h+=op[1];c=op[2];if(c===a)c=r;}
if(!hit){ok=false;break;}}if(ok)out.push({a:labels[a],r:labels[r],longest});
}}
return out;
}
if (require.main === module) {
 const fs = require("node:fs"), path = require("node:path");
 const data = JSON.parse(fs.readFileSync(path.join(__dirname,"data.json"),"utf8"));
 const coreText = fs.readFileSync(path.join(__dirname,"verification_core.js"),"utf8");
 let final = {};
 for (const name of ["primary","permuted"]) {
  const text = name==="primary"?coreText:coreText.replace("PHYSICAL=[6,2,0,4,3,7,8,5,1]","PHYSICAL=[6,3,0,2,4,8,7,5,1]");
  const core = new Function(text+";return {contracts,step,matches,rowsOf};")();
  const g = gather(core,data[name],data.sites,data.instructions,name==="primary"?58154:56158);
  const r = searchLocal(data[name],g.patterns,6,120,name==="permuted");
  final[name] = {contexts:g.stats,local:{found:r.found,offsets:r.offsets,states:r.states,window:6,stepBound:120}};
  if(name==="permuted"){
   final.permuted.bypass=bypass(data[name],g.patterns);
   if(process.argv.includes("--extended")){
    const old=Object.fromEntries(data[name].map(([q,b,w,d,n])=>[q*2+b,[w,d?1:-1,n]])),rewrites=[];
    for(let i=0;i<r.labels.length;i++)for(let b=0;b<2;b++)for(const[ai,desc]of Object.entries(r.sol[i][b])){
     let[w,d,t]=r.acts[ai],a=[w,d,r.labels[t]===undefined?254:r.labels[t]],q=r.labels[i];
     if(a.some((v,k)=>v!==old[q*2+b][k]))rewrites.push({q,b,action:a,max:desc.max});
    }
    const positives=[];
    for(let i=0;i<rewrites.length;i++){
     const m=rewrites[i],lines=data[name].map(x=>x[0]===m.q&&x[1]===m.b?[x[0],x[1],m.action[0],m.action[1]===1,m.action[2]]:x);
     const direct=directSearch(lines,g.patterns),local=searchLocal(lines,g.patterns);
     if(direct.length||local.found.length)positives.push({i,m,direct,contextual:local.found});
     if(i%50===0)console.error("Rewrites checked:",i,"/",rewrites.length);
    }
    final.permuted.rewrites={examined:rewrites.length,positives};
   }
  }
 }
 console.log(JSON.stringify(final,null,2));
}
module.exports={gather,searchLocal,bypass,directSearch};

