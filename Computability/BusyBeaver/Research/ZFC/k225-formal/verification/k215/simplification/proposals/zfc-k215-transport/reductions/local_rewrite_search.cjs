#!/usr/bin/env node
// Bounded exact local diagrams for CM215. No lower-bound claim.
// Uses an inductive finite-window overapproximation reachable from initial
// control on every initial tape. Leaving window or fuel is inconclusive.
const fs=require('node:fs'),crypto=require('node:crypto');
const path=require('node:path');
const input=process.argv[2],out=process.argv[3],rad=Number(process.argv[4]||4),fuel=Number(process.argv[5]||33);
if(!input||!out)throw Error('usage: node local_rewrite_search.cjs TABLE OUTPUT [RADIUS] [FUEL]');
const raw=fs.readFileSync(input,'utf8'),T=new Map();let start;
for(const line of raw.split(/\r?\n/)){if(line.startsWith('#! start ')){start=Number(line.slice(9));continue;}if(!line||line[0]==='#')continue;
 const[q,b,w,d,z]=line.split(/\s+/);T.set(2*Number(q)+Number(b),[Number(w),d==='R'?1:-1,Number(z)]);}
const Q=[...new Set([...T.keys()].map(k=>Math.floor(k/2)))].sort((a,b)=>a-b),index=new Map(Q.map((q,i)=>[q,i]));
const halt=254,W=1<<(2*rad+1),mask=W-1,hi=1<<(2*rad),mid=1<<rad;
const dom=Q.map(()=>new Uint8Array(W)),queue=[];let head=0;
function add(q,w){if(q===halt)return;const i=index.get(q);if(i===undefined)throw Error('target');if(dom[i][w])return;dom[i][w]=1;queue.push(i*W+w);}
for(let w=0;w<W;w++)add(start,w);
while(head<queue.length){const k=queue[head++],i=Math.floor(k/W),w=k%W,q=Q[i],b=!!(w&mid),[wr,dir,z]=T.get(q*2+Number(b)),v=(w&~mid)|(wr*mid);
 if(dir===1){add(z,v>>>1);add(z,(v>>>1)|hi);}else{add(z,(v<<1)&mask);add(z,((v<<1)&mask)|1);}}
const words=new Map();for(const q of Q)for(let b=0;b<2;b++){let a=[];const dd=dom[index.get(q)];for(let w=0;w<W;w++)if(dd[w]&&Number(!!(w&mid))===b)a.push(w);if(a.length>2)a=[a[0],a[a.length-1],...a.slice(1,-1)];words.set(q*2+b,a);}
const oldcache=new Map();
function step(q,h,m,act){const[w,d,z]=act;return[z,h+d,(m&~(1<<(h+rad)))|(w<<(h+rad))];}
function oldpath(q,word){const kk=q*W+word;if(oldcache.has(kk))return oldcache.get(kk);let a=[],h=0,m=word;
 for(let k=1;k<=fuel;k++){if(q===halt||h < -rad||h>rad)break;[q,h,m]=step(q,h,m,T.get(q*2+((m>>>(h+rad))&1)));a.push([q,h,m]);}
 if(oldcache.size>=2000)oldcache.clear();oldcache.set(kk,a);return a;}
function key(q,h,m){return q*(2*rad+7)*W+(h+rad+3)*W+m;}
function rowcheck(k,act){const q0=Math.floor(k/2);
 for(const word of words.get(k)){const goals=new Set(oldpath(q0,word).map(([q,h,m])=>key(q,h,m)));let q=q0,h=0,m=word,ok=false,seen=new Set();
  for(let n=1;n<=fuel;n++){if(q===halt||h < -rad||h>rad)break;let st=key(q,h,m);if(seen.has(st))break;seen.add(st);let row=q*2+((m>>>(h+rad))&1);[q,h,m]=step(q,h,m,row===k?act:T.get(row));if(goals.has(key(q,h,m))){ok=true;break;}}
  if(!ok)return false;}return true;}
const began=Date.now(),A=new Map([...T].map(([k,a])=>[k,[a]])),hits=[];let attempted=0;
for(const q of Q){for(let b=0;b<2;b++){const k=q*2+b,old=T.get(k);for(let w=0;w<2;w++)for(const d of[-1,1])for(const z of[...Q,halt]){const act=[w,d,z];if(act.every((v,j)=>v===old[j]))continue;attempted++;if(rowcheck(k,act)){A.get(k).push(act);hits.push({row:[q,b],old,new:act});}}}
}
const foldattempts=[],foldhits=[];
function foldcheck(N,keep,drop){const phi=q=>q===drop?keep:q;
 for(const q0 of[keep,drop])for(let b=0;b<2;b++)for(const word of words.get(q0*2+b)){const goals=new Set(oldpath(q0,word).map(([q,h,m])=>key(phi(q),h,m)));let q=phi(q0),h=0,m=word,ok=false,seen=new Set();
  for(let n=1;n<=fuel;n++){if(q===halt||h < -rad||h>rad)break;let st=key(q,h,m);if(seen.has(st))break;seen.add(st);[q,h,m]=step(q,h,m,N.get(q*2+((m>>>(h+rad))&1)));if(goals.has(key(q,h,m))){ok=true;break;}}
  if(!ok)return false;}return true;}
for(const keep of Q)for(const drop of Q){if(keep===drop)continue;const phi=q=>q===drop?keep:q,opts=[];
 for(let b=0;b<2;b++){const left=new Map(A.get(keep*2+b).map(([w,d,z])=>[[w,d,phi(z)].join(','),[w,d,phi(z)]])),right=new Set(A.get(drop*2+b).map(([w,d,z])=>[w,d,phi(z)].join(',')));opts.push([...left].filter(([k,v])=>right.has(k)).map(([k,v])=>v));}
 if(opts.some(a=>!a.length))continue;
 for(const a0 of opts[0])for(const a1 of opts[1]){const N=new Map([...T].filter(([k,v])=>Math.floor(k/2)!==drop).map(([k,[w,d,z]])=>[k,[w,d,phi(z)]]));N.set(keep*2,a0);N.set(keep*2+1,a1);let desc={keep,drop,actions:[a0,a1]};foldattempts.push(desc);if(foldcheck(N,keep,drop))foldhits.push(desc);}}

const eliminated=[],partial=[],elimFailures=[],allTargets=[...Q,halt];let elimAttempts=0;
for(const drop of Q){if(drop===start)continue;
 const entrances=[...T].filter(([k,a])=>Math.floor(k/2)!==drop&&a[2]===drop).map(([k,a])=>k),blocked=new Set(entrances);
 const choices=[];let failed=null;
 for(const row of entrances){const q0=Math.floor(row/2),options=[];
  function eliminateCheck(act){
   for(const word of words.get(row)){const goals=new Set(oldpath(q0,word).filter(([q,h,m])=>q!==drop).map(([q,h,m])=>key(q,h,m)));let q=q0,h=0,m=word,ok=false,seen=new Set();
    for(let n=1;n<=fuel;n++){if(q===halt||q===drop||h < -rad||h>rad)break;const k=q*2+((m>>>(h+rad))&1);if(n>1&&blocked.has(k)&&k!==row)break;const st=key(q,h,m);if(seen.has(st))break;seen.add(st);[q,h,m]=step(q,h,m,k===row?act:T.get(k));if(goals.has(key(q,h,m))){ok=true;break;}}
    if(!ok)return false;}return true;}
  for(let w=0;w<2;w++)for(const d of[-1,1])for(const z of allTargets){if(z===drop)continue;elimAttempts++;const act=[w,d,z];if(eliminateCheck(act))options.push(act);}
  if(!options.length){failed=row;break;}choices.push({row:[q0,row%2],options});
 }
 if(failed===null)eliminated.push({drop,choices});
 else{elimFailures.push({drop,failed:[Math.floor(failed/2),failed%2]});if(choices.length)partial.push({drop,choices,failed:[Math.floor(failed/2),failed%2]});}
}


const receipt={status:'COMPLETE_BOUNDED_REWRITE_CLOSURE_SEARCH',sha256:crypto.createHash('sha256').update(raw).digest('hex'),radius:rad,fuel,domain_contexts:queue.length,row_candidates:attempted,row_rewrites:hits,fold_candidates:foldattempts,fold_hits:foldhits,elimination_attempts:elimAttempts,elimination_hits:eliminated,elimination_partial:partial,elimination_first_failures:elimFailures,seconds:(Date.now()-began)/1000,scope:'One-row stuttering rewrites, two-row rewrite-closure folds, and independent-entrance state deletion. Deletion candidates may change every external entrance, and paths must join at a retained old state before executing another changed entrance. Candidate folds jointly checked against mapped old positive paths. Finite-window and fuel failures are inconclusive, not semantic rejection or a minimality theorem. Any hit requires independent replay.'};
fs.writeFileSync(out,JSON.stringify(receipt,null,2)+'\n');console.log(JSON.stringify({...receipt,row_rewrites:hits.length,fold_candidates:foldattempts.length,elimination_first_failures:elimFailures.length},null,2));
