// Bounded sufficient state-reduction searches. No negative result is a global lower bound.
function localSearch(tableText, cfg={}) {
  const K=cfg.radius??6, STEP=cfg.maxSteps??256, start=cfg.start??74;
  const raw=tableText.trim().split(/\n/).filter(s=>s.trim()&&!s.startsWith("#")).map(s=>s.trim().split(/\s+/));
  const states=Array.from(new Set(raw.map(x=>+x[0]))).sort((a,b)=>a-b), ix=new Map(states.map((q,i)=>[q,i]));
  const halts=Array.from(new Set(raw.map(x=>+x[4]).filter(q=>!ix.has(q)))); if(halts.length!==1)throw Error("one halt expected");
  const rows=states.map(()=>[null,null]);for(const [q,b,w,d,n] of raw)rows[ix.get(+q)][+b]=[+w,d==="R"?1:-1,ix.has(+n)?ix.get(+n):-1];
  const W=2*K+1,N=1<<W,MASK=N-1,reach=states.map(()=>new Uint8Array(N)),queue=[];
  function add(q,p){if(q<0||reach[q][p])return;reach[q][p]=1;queue.push(q*N+p);}
  if(cfg.blankOnly)add(ix.get(start),0);else for(let p=0;p<N;p++)add(ix.get(start),p);
  for(let j=0;j<queue.length;j++){const q=Math.floor(queue[j]/N);let p=queue[j]%N;const [w,d,n]=rows[q][(p>>K)&1];p=(p&~(1<<K))|(w<<K);if(d===1){const v=p>>1;add(n,v);add(n,v|(1<<(W-1)));}else{const v=(p<<1)&MASK;add(n,v);add(n,v|1);}}
  const patterns=states.map(()=>[[],[]]);for(let q=0;q<states.length;q++)for(let p=0;p<N;p++)if(reach[q][p])patterns[q][(p>>K)&1].push(p);
  const actions=[];for(let n=-1;n<states.length;n++)for(let w=0;w<2;w++)for(const d of [-1,1])actions.push([w,d,n]);
  function choices(q,b,other=-2,aliasEndpoint=false){
    const [ow,od,on]=rows[q][b],out=new Map();
    for(let ai=0;ai<actions.length;ai++){const [fw,fd,fn]=actions[ai];let ok=true,maxst=0;const visits=new Set();
      for(const p of patterns[q][b]){const targetp=(p&~(1<<K))|(ow<<K);let c=fn,h=fd,t=(p&~(1<<K))|(fw<<K),hit=false;
        for(let st=1;st<=STEP;st++){
          if((c===on||(aliasEndpoint&&(c===q||c===other)))&&h===od&&t===targetp){hit=true;maxst=Math.max(maxst,st);break;}
          if(c===q||c===other||h < -K||h>K||c<0)break;
          visits.add(c);const [w,d,n]=rows[c][(t>>(h+K))&1];t=(t&~(1<<(h+K)))|(w<<(h+K));h+=d;c=n;
        }if(!hit){ok=false;break;}
      }if(ok)out.set(ai,{visits,maxst});
    }return out;
  }
  const ordinary=states.map((q,i)=>[choices(i,0),choices(i,1)]);
  const hits=[];let specialCalls=0;
  function pairChoices(q,b,other){if(cfg.moduloAlias!==false&&(rows[q][b][2]===q||rows[q][b][2]===other)){specialCalls++;return choices(q,b,other,true);}return new Map(Array.from(ordinary[q][b]).filter(([a,g])=>!g.visits.has(other)));}
  for(let a=0;a<states.length;a++)for(let r=a+1;r<states.length;r++){
    if(cfg.excludeStart&&(states[a]===start||states[r]===start))continue;
    if(patterns[a][0].length+patterns[a][1].length===0||patterns[r][0].length+patterns[r][1].length===0)continue;
    const result=[[],[]];
    for(let b=0;b<2;b++){
      const am=pairChoices(a,b,r),rm=pairChoices(r,b,a);
      const normalize=ai=>{const [w,d,n]=actions[ai];return ((n===a?r:n)+1)*4+w*2+(d===1?1:0);};
      const aa=new Map(Array.from(am,([ai,g])=>[normalize(ai),g.maxst])),rr=new Map(Array.from(rm,([ai,g])=>[normalize(ai),g.maxst]));
      for(const [ai,st] of aa)if(rr.has(ai)){const [w,d,n]=actions[ai];result[b].push({action:[w,d,n<0?halts[0]:states[n]],steps:Math.max(st,rr.get(ai))});}
      if(!result[b].length)break;
    }if(result.every(x=>x.length))hits.push({remove:states[a],keep:states[r],choices:result});
  }
  return {states:states.length,radius:K,maxSteps:STEP,blankOnly:!!cfg.blankOnly,moduloAlias:cfg.moduloAlias!==false,excludeStart:!!cfg.excludeStart,reachableAbstractContexts:queue.length,specialCalls,hits};
}
const buildModel=function localSearch(tableText, cfg={}) {
  const K=cfg.radius??6, STEP=cfg.maxSteps??256, start=cfg.start??74;
  const raw=tableText.trim().split(/\n/).filter(s=>s.trim()&&!s.startsWith("#")).map(s=>s.trim().split(/\s+/));
  const states=Array.from(new Set(raw.map(x=>+x[0]))).sort((a,b)=>a-b), ix=new Map(states.map((q,i)=>[q,i]));
  const halts=Array.from(new Set(raw.map(x=>+x[4]).filter(q=>!ix.has(q)))); if(halts.length!==1)throw Error("one halt expected");
  const rows=states.map(()=>[null,null]);for(const [q,b,w,d,n] of raw)rows[ix.get(+q)][+b]=[+w,d==="R"?1:-1,ix.has(+n)?ix.get(+n):-1];
  const W=2*K+1,N=1<<W,MASK=N-1,reach=states.map(()=>new Uint8Array(N)),queue=[];
  function add(q,p){if(q<0||reach[q][p])return;reach[q][p]=1;queue.push(q*N+p);}
  if(cfg.blankOnly)add(ix.get(start),0);else for(let p=0;p<N;p++)add(ix.get(start),p);
  for(let j=0;j<queue.length;j++){const q=Math.floor(queue[j]/N);let p=queue[j]%N;const [w,d,n]=rows[q][(p>>K)&1];p=(p&~(1<<K))|(w<<K);if(d===1){const v=p>>1;add(n,v);add(n,v|(1<<(W-1)));}else{const v=(p<<1)&MASK;add(n,v);add(n,v|1);}}
  const patterns=states.map(()=>[[],[]]);for(let q=0;q<states.length;q++)for(let p=0;p<N;p++)if(reach[q][p])patterns[q][(p>>K)&1].push(p);
  const actions=[];for(let n=-1;n<states.length;n++)for(let w=0;w<2;w++)for(const d of [-1,1])actions.push([w,d,n]);
  function choices(q,b,other=-2,aliasEndpoint=false){
    const [ow,od,on]=rows[q][b],out=new Map();
    for(let ai=0;ai<actions.length;ai++){const [fw,fd,fn]=actions[ai];let ok=true,maxst=0;const visits=new Set();
      for(const p of patterns[q][b]){const targetp=(p&~(1<<K))|(ow<<K);let c=fn,h=fd,t=(p&~(1<<K))|(fw<<K),hit=false;
        for(let st=1;st<=STEP;st++){
          if((c===on||(aliasEndpoint&&(c===q||c===other)))&&h===od&&t===targetp){hit=true;maxst=Math.max(maxst,st);break;}
          if(c===q||c===other||h < -K||h>K||c<0)break;
          visits.add(c);const [w,d,n]=rows[c][(t>>(h+K))&1];t=(t&~(1<<(h+K)))|(w<<(h+K));h+=d;c=n;
        }if(!hit){ok=false;break;}
      }if(ok)out.set(ai,{visits,maxst});
    }return out;
  }
  const ordinary=states.map((q,i)=>[choices(i,0),choices(i,1)]);
  return {dat:{states,rows,patterns,K,N,W,MASK,start,halt:halts[0]},ordinary:ordinary.map(p=>p.map(m=>Object.fromEntries(Array.from(m,([i,g])=>[i,1])))),actions};
};
function shiftSearch(dat, ordinary, actions, STEP=256) {
 const {states,rows,patterns,K}=dat;
 const incoming=states.map(()=>[]);
 for(let s=0;s<rows.length;s++)for(let b=0;b<2;b++)if(rows[s][b][2]>=0)incoming[rows[s][b][2]].push([s,b,rows[s][b][1]]);
 const shifted=states.map((s,q)=>[-2,2].map(sh=>{const p=[[],[]];for(let ob=0;ob<2;ob++)for(const x of patterns[q][ob])p[(x>>(K+sh))&1].push([x,ob]);return p;}));
 const hits=[];let pairs=0,tested=0;
 for(let q=0;q<states.length;q++)for(let r=0;r<states.length;r++){if(q===r)continue;
 for(let si=0;si<2;si++){const shift=si?2:-2;
 if(incoming[q].some(([s,b,d])=>s!==q&&s!==r&&(d+shift!==1&&d+shift!==-1)))continue;
 pairs++;const choices=[[],[]],qgroups=shifted[q][si];
 function one(old,initShift,p,ob,action){const [fw,fd,fn]=action;if(fn===q)return 0;
 const [ow,od,on]=rows[old][ob],targetp=(p&~(1<<K))|(ow<<K),targeth=od+(on===q?shift:0),targetq=on===q?r:on;
 let c=fn,h=initShift+fd,t=(p&~(1<<(K+initShift)))|(fw<<(K+initShift));
 let prev0=-1,prev1=-2,prev2=-3,prev3=-4;
 for(let st=1;st<=STEP;st++){
 if(c===targetq&&h===targeth&&t===targetp)return st;
 if(c===r||c===q||h < -K||h>K||c<0)return 0;
 const signature=(c*(2*K+1)+h+K)*dat.N+t;
 if(signature===prev0||signature===prev1||signature===prev2||signature===prev3)return 0;
 prev3=prev2;prev2=prev1;prev1=prev0;prev0=signature;
 let [w,d,n]=rows[c][(t>>(h+K))&1];if(n===q){n=r;d+=shift;}
 t=(t&~(1<<(h+K)))|(w<<(h+K));h+=d;c=n;
 }return 0;}
 const order=qgroups[0].length>=qgroups[1].length?[0,1]:[1,0];
 for(const b of order){
 const target=rows[r][b][2];
 const ais=(target===q||target===r)?actions.map((_,i)=>i):Object.keys(ordinary[r][b]).map(Number);
 for(const ai of ais){tested++;const act=actions[ai];if(act[2]===q)continue;let valid=true,maxSteps=0;
 // Cheap samples from both obligations before full finite verification.
 for(let j=0;j<4;j++){
 if(qgroups[b].length>j){const [p,ob]=qgroups[b][j],steps=one(q,shift,p,ob,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}
 if(patterns[r][b].length>j){const steps=one(r,0,patterns[r][b][j],b,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}
 }if(!valid)continue;
 for(let j=4;j<qgroups[b].length;j++){const [p,ob]=qgroups[b][j],steps=one(q,shift,p,ob,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}if(!valid)continue;
 for(let j=4;j<patterns[r][b].length;j++){const steps=one(r,0,patterns[r][b][j],b,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}if(!valid)continue;
 choices[b].push({action:act.map((v,i)=>i===2?(v<0?dat.halt:states[v]):v),maxSteps});
 }
 if(!choices[b].length)break;
 }
 if(choices.every(c=>c.length))hits.push({remove:states[q],keep:states[r],headShift:shift,choices});
 }}
 return {radius:K,maxSteps:STEP,pairs,actionsTested:tested,hits};
}
function gaugeSearch(dat, ordinary, actions, STEP=256) {
 const {states,rows,patterns,K,start}=dat;
 const incoming=states.map(()=>[]);
 for(let s=0;s<rows.length;s++)for(let b=0;b<2;b++)if(rows[s][b][2]>=0)incoming[rows[s][b][2]].push([s,b,rows[s][b][1]]);
 const hits=[];let pairs=0,tested=0;
 for(let q=0;q<states.length;q++)for(let r=0;r<states.length;r++){if(q===r||states[q]===start)continue;
 for(const offset of [-1,1]){
 if(incoming[q].some(([s,b,d])=>s!==q&&s!==r&&d!==-offset))continue;
 pairs++;const choices=[[],[]];
 function one(old,p,ob,action){const [fw,fd,fn]=action;if(fn===q)return 0;
 const [ow,od,on]=rows[old][ob];let targetp=(p&~(1<<K))|(ow<<K);
 if(on===q)targetp^=1<<(K+od+offset);
 const targeth=od,targetq=on===q?r:on;
 let initial=p;if(old===q)initial^=1<<(K+offset);
 let c=fn,h=fd,t=(initial&~(1<<K))|(fw<<K);
 let prev0=-1,prev1=-2,prev2=-3,prev3=-4;
 for(let st=1;st<=STEP;st++){
 if(c===targetq&&h===targeth&&t===targetp)return st;
 if(c===r||c===q||h < -K||h>K||c<0)return 0;
 const signature=(c*(2*K+1)+h+K)*dat.N+t;
 if(signature===prev0||signature===prev1||signature===prev2||signature===prev3)return 0;
 prev3=prev2;prev2=prev1;prev1=prev0;prev0=signature;
 let [w,d,n]=rows[c][(t>>(h+K))&1];if(n===q){n=r;w^=1;}
 t=(t&~(1<<(h+K)))|(w<<(h+K));h+=d;c=n;
 }return 0;}
 const order=patterns[q][0].length>=patterns[q][1].length?[0,1]:[1,0];
 for(const b of order){
 const target=rows[r][b][2];
 const ais=(target===q||target===r)?actions.map((_,i)=>i):Object.keys(ordinary[r][b]).map(Number);
 for(const ai of ais){tested++;const act=actions[ai];if(act[2]===q)continue;let valid=true,maxSteps=0;
 for(let j=0;j<4;j++){
 if(patterns[q][b].length>j){const steps=one(q,patterns[q][b][j],b,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}
 if(patterns[r][b].length>j){const steps=one(r,patterns[r][b][j],b,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}
 }if(!valid)continue;
 for(let j=4;j<patterns[q][b].length;j++){const steps=one(q,patterns[q][b][j],b,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}if(!valid)continue;
 for(let j=4;j<patterns[r][b].length;j++){const steps=one(r,patterns[r][b][j],b,act);if(!steps){valid=false;break;}maxSteps=Math.max(maxSteps,steps);}if(!valid)continue;
 choices[b].push({action:act.map((v,i)=>i===2?(v<0?dat.halt:states[v]):v),maxSteps});
 }
 if(!choices[b].length)break;
 }
 if(choices.every(c=>c.length))hits.push({remove:states[q],keep:states[r],flippedOffset:offset,choices});
 }}
 return {radius:K,maxSteps:STEP,pairs,actionsTested:tested,hits};
}
if (typeof require !== 'undefined' && require.main === module) {
 const fs=require('node:fs');
 const [path,startArg,radiusArg='6',stepsArg='256']=process.argv.slice(2);
 if(!path||startArg===undefined)throw Error('Usage: node search.cjs TABLE.tm START [RADIUS] [MAX_STEPS]');
 const text=fs.readFileSync(path,'utf8'),cfg={start:+startArg,radius:+radiusArg,maxSteps:+stepsArg};
 if(!Number.isInteger(cfg.radius)||cfg.radius<2||cfg.radius>9)throw Error('Use radius 2..9');
 const local=localSearch(text,cfg),m=buildModel(text,cfg);
 const shifted=shiftSearch(m.dat,m.ordinary,m.actions,cfg.maxSteps);
 const marker=gaugeSearch(m.dat,m.ordinary,m.actions,cfg.maxSteps);
 console.log(JSON.stringify({local,shifted,marker},null,2));
}
