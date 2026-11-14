// Bounded neutral-rewrite and merge search. No lower-bound claim.
// Usage: node neutral_search.mjs reference/pa194.native.tm
import fs from "node:fs";
import crypto from "node:crypto";

const input = fs.readFileSync(process.argv[2], "utf8");
const states = [], rows = new Int32Array(5000);
const exists = new Uint8Array(2500);
for (const line of input.trim().split(/\r?\n/)) {
  if (!line.trim() || line.startsWith("#")) continue;
  let [q,b,w,d,n] = line.trim().split(/\s+/);
  q=+q; b=+b; w=+w; n=+n;
  if (!(q>=0 && q<2500 && [0,1].includes(b) &&
        [0,1].includes(w) && ["L","R"].includes(d))) {
    throw Error("Invalid row: " + line);
  }
  if (!exists[q]) { states.push(q); exists[q]=1; }
  rows[2*q+b] = 4*n+2*w+(d==="R"?1:0);
}
states.sort((a,b)=>a-b);

function analyze(rows,states,exists,K=4) {
  const W=2*K+1,N=1<<W,MASK=N-1;
  const idx=new Int32Array(2500);
  states.forEach((q,i)=>idx[q]=i);
  const reached=new Uint8Array(states.length*N), queue=[];
  function add(q,p) {
    if (!exists[q]) return;
    const x=idx[q]*N+p;
    if (!reached[x]) { reached[x]=1; queue.push(x); }
  }
  for (let p=0;p<N;p++) add(74,p);
  for (let i=0;i<queue.length;i++) {
    const x=queue[i],q=states[Math.floor(x/N)];
    let p=x%N,ac=rows[2*q+((p>>K)&1)];
    p=(p&~(1<<K))|(((ac>>1)&1)<<K);
    const target=ac>>2;
    if (ac&1) {
      const v=p>>1; add(target,v); add(target,v|(1<<(W-1)));
    } else {
      const v=(p<<1)&MASK; add(target,v); add(target,v|1);
    }
  }
  const patterns={};
  for (const q of states) {
    patterns[q]=[[],[]];
    for (let p=0;p<N;p++)
      if (reached[idx[q]*N+p]) patterns[q][(p>>K)&1].push(p);
  }
  const actions=[];
  for (const q of states)
    for (let w=0;w<2;w++)
      for (let d=0;d<2;d++) actions.push(4*q+2*w+d);

  const solutions={};
  for (const q of states) {
    const sol=[{},{}];
    for (let b=0;b<2;b++) {
      const old=rows[2*q+b],oldN=old>>2;
      const oldD=(old&1)?1:-1,oldW=(old>>1)&1;
      for (let ai=0;ai<actions.length;ai++) {
        const first=actions[ai],vis=new Set();
        let okay=true,maxsteps=0;
        for (const p of patterns[q][b]) {
          const targetp=(p&~(1<<K))|(oldW<<K);
          let c=first>>2,h=(first&1)?1:-1;
          let t=(p&~(1<<K))|(((first>>1)&1)<<K),hit=false;
          for (let st=1;st<=80;st++) {
            if (c===oldN && h===oldD && t===targetp) {
              hit=true; maxsteps=Math.max(maxsteps,st); break;
            }
            if (c===q || h < -K || h>K ||
                c<0 || c>=2500 || !exists[c]) break;
            vis.add(c);
            const op=rows[2*c+((t>>(h+K))&1)];
            t=(t&~(1<<(h+K)))|(((op>>1)&1)<<(h+K));
            h+=(op&1)?1:-1; c=op>>2;
          }
          if (!hit) { okay=false; break; }
        }
        if (okay)
          sol[b][ai]={visited:[...vis],steps:maxsteps};
      }
    }
    solutions[q]=sol;
  }

  const pairs=[];
  for (let i=0;i<states.length;i++)
    for (let j=i+1;j<states.length;j++) {
      const a=states[i],b=states[j];
      if (a===74 || b===74) continue;
      const choices=[[],[]];
      for (let bit=0;bit<2;bit++)
        for (const [ai,ga] of Object.entries(solutions[a][bit])) {
          const gb=solutions[b][bit][ai];
          if (gb && !ga.visited.includes(b) &&
                    !gb.visited.includes(a))
            choices[bit].push(actions[+ai]);
        }
      if (choices[0].length && choices[1].length)
        pairs.push({remove:a,keep:b,choices});
    }
  return {contexts:queue.length,solutions,pairs,actions};
}

const baseline=analyze(rows,states,exists);
const patches=[];
for (const q of states)
  for (let b=0;b<2;b++)
    for (const ai of Object.keys(baseline.solutions[q][b])) {
      const ac=baseline.actions[+ai];
      if (ac!==rows[2*q+b]) patches.push([q,b,ac]);
    }

const hits=[];
let tested=0;
for (const [q,b,ac] of patches) {
  const old=rows[2*q+b];
  rows[2*q+b]=ac;
  const result=analyze(rows,states,exists);
  if (result.pairs.length)
    hits.push({patch:[q,b,ac],pairs:result.pairs,
               contexts:result.contexts});
  rows[2*q+b]=old;
  tested++;
}
console.log(JSON.stringify({
  inputSHA256:crypto.createHash("sha256").update(input).digest("hex"),
  start:74,radius:4,maxDetourSteps:80,
  workingStates:states.length,
  baselineContexts:baseline.contexts,
  baselinePairs:baseline.pairs,
  patches:patches.length,tested,hits,
  scope:"Bounded sufficient local rewrite search; not a lower bound."
},null,2));
