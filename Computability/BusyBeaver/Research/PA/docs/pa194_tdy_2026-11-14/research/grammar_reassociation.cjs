// Deterministic replay of the 7,438 scored occurrence-rotation proposals.
// Scope: this finite grammar scoring heuristic, not a minimality proof.
const fs=require('node:fs');
function engine(fixed){
const macros={node65:90,node55:98,node58:12,node70:166,node49:19,node72:69,node75:213,node142:194,node150:221,I:61,node60:99,node61:190};
function build(t){
 let rows=new Map(fixed.map(([q,b,w,d,n])=>[q*2+b,[w,d,n]])),shape=new Map(),index=new Map(),seq=2000;
 function state(t){
  if(typeof t==="string")return macros[t];
  let key=JSON.stringify(t);
  if(key==='["I","I"]')return 99;
  if(key==='[["I","I"],["I","I"]]')return 190;
  if(index.has(key))return index.get(key);
  let q=seq++;index.set(key,q);shape.set(q,t);
  for(let b=0;b<2;b++)rows.set(q*2+b,t[b]==="X"?[0,false,302]:[b,true,state(t[b])]);
  return q;
 }
 let root=state(t);rows.set(203,[1,true,root]);return {rows,shape,root};
}
const actsKey=x=>x[0]+","+Number(x[1])+","+x[2];
function opsFn(rows,shape){
 let incoming=new Map();
 for(let [key,[w,d,n]] of rows)if(d&&w==key%2&&shape.has(n)){if(!incoming.has(n))incoming.set(n,new Set());incoming.get(n).add(w);}
 let providers=[new Map(),new Map()];
 for(let key of rows.keys()){if(key%2)continue;let h=key/2,[w0,d0,u0]=rows.get(key),[w1,d1,u1]=rows.get(key+1);
 if(w0||w1!==1||!d0||!d1)continue;
 for(let b=0;b<2;b++)if(rows.has(u0*2+b)&&rows.has(u1*2+b)){
 let k=actsKey(rows.get(u0*2+b))+"|"+actsKey(rows.get(u1*2+b));if(!providers[b].has(k))providers[b].set(k,[]);providers[b].get(k).push([h,u0,u1]);}}
 let left=[...shape.keys()].filter(q=>incoming.get(q)?.size===1&&incoming.get(q).has(0)),right=[...shape.keys()].filter(q=>incoming.get(q)?.size===1&&incoming.get(q).has(1)),ops=[];
 for(let a of left)for(let b of right){let opts=[];
 for(let bit=0;bit<2;bit++){let a0=rows.get(a*2+bit),b0=rows.get(b*2+bit),k=actsKey(a0)+"|"+actsKey(b0);
 if(actsKey(a0)===actsKey(b0))opts.push([a0]);
 else opts.push((providers[bit].get(k)||[]).filter(x=>!x.includes(a)&&!x.includes(b)).map(([h])=>[bit,false,h]));}
 if(opts.every(x=>x.length))ops.push([a,b,opts]);}
 return ops;
}
function matching(ops){
 let edges=new Map(),match=new Map();
 for(let[a,b]of ops){if(!edges.has(a))edges.set(a,[]);edges.get(a).push(b);}
 function augment(a,seen){for(let b of edges.get(a)){if(seen.has(b))continue;seen.add(b);if(!match.has(b)||augment(match.get(b),seen)){match.set(b,a);return true;}}return false;}
 for(let a of edges.keys())augment(a,new Set());return [...match].map(([b,a])=>[a,b]);
}
function cost(t){let z=build(t),ops=opsFn(z.rows,z.shape),pairs=matching(ops);return {n:z.rows.size/2-pairs.length,raw:z.rows.size/2,pairs,ops,rows:z.rows,shape:z.shape};}
function paths(t,p=[],arr=[]){if(Array.isArray(t)){arr.push(p);paths(t[0],p.concat(0),arr);paths(t[1],p.concat(1),arr);}return arr;}
function get(t,p){for(let b of p)t=t[b];return t;}
function put(t,p,v){if(!p.length)return v;let a=t.slice();a[p[0]]=put(t[p[0]],p.slice(1),v);return a;}
function rotate(t,p,r){let n=get(t,p);return put(t,p,r?[n[0][0],[n[0][1],n[1]]]:[[n[0],n[1][0]],n[1][1]]);}
return {build,cost,paths,get,put,rotate};
}
const fixed=[[0,0,1,true,94],[0,1,1,true,0],[1,0,0,false,1],[1,1,1,false,2],[2,0,0,false,3],[2,1,1,false,2],[3,0,0,false,5],[3,1,1,false,2],[4,0,1,true,6],[4,1,0,false,4],[5,0,0,false,9],[5,1,1,false,2],[6,0,0,true,6],[6,1,0,true,10],[8,0,0,true,14],[8,1,1,true,13],[9,0,0,false,15],[9,1,1,false,2],[10,0,0,false,16],[10,1,0,true,10],[11,0,0,false,26],[11,1,1,true,18],[12,0,0,true,19],[12,1,1,true,20],[13,0,0,false,91],[13,1,1,false,31],[14,0,0,false,11],[14,1,0,true,22],[15,0,0,false,23],[15,1,1,false,2],[16,0,1,false,1],[16,1,0,false,1],[17,0,0,true,24],[17,1,0,true,32],[18,0,0,true,96],[18,1,0,false,108],[19,0,0,true,28],[19,1,1,true,29],[20,0,0,true,30],[20,1,1,true,31],[21,0,0,true,24],[21,1,0,true,60],[22,0,0,true,33],[22,1,1,true,22],[23,0,0,false,34],[23,1,1,false,2],[24,0,0,false,35],[24,1,0,true,0],[25,0,0,true,36],[25,1,1,true,25],[26,0,0,true,194],[26,1,1,true,42],[27,0,0,true,39],[27,1,0,false,40],[28,0,0,true,41],[28,1,1,true,42],[29,0,0,true,43],[29,1,1,true,44],[30,0,0,true,45],[30,1,1,true,46],[31,0,0,true,21],[31,1,1,true,47],[32,0,0,true,48],[32,1,1,true,32],[33,0,0,true,32],[33,1,1,true,33],[34,0,0,false,75],[34,1,1,false,2],[35,0,1,true,35],[35,1,1,false,1],[36,0,0,true,51],[36,1,1,true,36],[38,0,0,true,28],[38,1,1,true,20],[39,0,0,false,11],[39,1,0,true,36],[40,0,0,false,4],[40,1,1,false,54],[41,0,0,true,24],[41,1,0,true,25],[42,0,0,true,13],[42,1,0,false,16],[43,0,0,true,56],[43,1,1,true,57],[44,0,0,true,58],[44,1,1,true,59],[45,0,0,true,24],[45,1,0,true,55],[46,0,0,true,61],[46,1,1,true,62],[47,0,0,true,63],[47,1,0,false,16],[48,0,0,true,25],[48,1,1,true,48],[49,0,0,false,35],[49,1,0,true,64],[51,0,0,true,16],[51,1,1,true,51],[53,0,0,true,68],[53,1,1,true,69],[54,0,0,false,40],[54,1,1,false,54],[55,0,0,true,22],[55,1,1,true,55],[56,0,0,false,11],[56,1,0,true,51],[57,0,0,true,61],[57,1,0,false,16],[58,0,0,true,70],[58,1,1,true,71],[59,0,0,true,62],[59,1,1,true,72],[60,0,0,true,55],[60,1,1,true,60],[61,0,0,true,49],[61,1,0,true,25],[62,0,0,false,28],[62,1,1,false,73],[63,0,0,false,123],[63,1,1,false,30],[64,0,0,true,74],[64,1,1,true,64],[66,0,1,true,198],[66,1,1,false,54],[68,0,0,true,77],[68,1,1,true,254],[69,0,0,false,213],[69,1,1,true,31],[70,0,0,true,41],[70,1,1,true,63],[71,0,0,false,91],[71,1,1,true,80],[72,0,0,true,56],[72,1,1,false,81],[73,0,0,true,82],[73,1,1,true,83],[74,0,1,true,0],[74,1,1,true,64],[75,0,0,true,75],[75,1,1,true,84],[77,0,0,true,87],[77,1,1,true,88],[80,0,0,true,91],[80,1,1,false,138],[81,0,0,false,111],[81,1,1,true,57],[82,0,0,true,49],[82,1,0,true,33],[83,0,0,true,93],[83,1,0,false,42],[84,0,0,true,53],[84,1,1,true,310],[87,0,0,true,301],[87,1,1,true,21],[88,0,0,true,122],[88,1,1,true,103],[90,0,0,true,105],[90,1,1,true,106],[91,0,0,true,82],[91,1,1,true,81],[92,0,0,true,104],[92,1,1,true,185],[93,0,0,true,108],[93,1,1,true,109],[94,0,0,true,66],[94,1,0,true,0],[95,0,0,true,27],[95,1,1,true,110],[96,0,0,true,101],[96,1,1,true,100],[97,0,1,false,113],[97,1,1,false,97],[98,0,0,true,19],[98,1,1,true,114],[99,0,0,true,61],[99,1,1,true,61],[100,0,0,true,174],[100,1,1,true,164],[101,0,0,false,26],[101,1,1,true,2000],[103,0,0,true,108],[103,1,0,false,302],[104,0,0,true,123],[104,1,1,true,124],[105,0,0,true,72],[105,1,1,true,59],[106,0,0,true,58],[106,1,1,true,125],[107,0,0,true,21],[107,1,1,true,126],[108,0,0,true,21],[108,1,0,false,10],[109,0,0,true,62],[109,1,1,true,42],[110,0,0,true,127],[110,1,1,true,8],[111,0,0,true,104],[111,1,1,true,128],[113,0,0,false,302],[113,1,0,false,97],[114,0,0,true,130],[114,1,1,true,107],[122,0,0,false,137],[122,1,0,false,1],[123,0,0,true,39],[123,1,1,true,73],[124,0,0,true,62],[124,1,1,true,138],[125,0,0,true,62],[125,1,1,true,139],[126,0,0,true,71],[126,1,0,false,16],[127,0,0,true,14],[127,1,1,true,138],[128,0,0,true,21],[128,1,1,true,141],[130,0,0,true,144],[130,1,1,false,20],[137,0,0,true,30],[137,1,1,true,70],[138,0,0,true,39],[138,1,1,false,130],[139,0,0,true,190],[139,1,0,false,16],[141,0,0,true,161],[141,1,0,false,16],[144,0,0,true,24],[144,1,0,true,48],[161,0,0,true,49],[161,1,0,true,32],[164,0,0,true,77],[164,1,1,true,98],[166,0,0,true,19],[166,1,1,true,179],[174,0,0,true,213],[174,1,1,true,28],[179,0,0,true,194],[179,1,1,true,128],[185,0,0,true,107],[185,1,1,true,98],[188,0,0,true,95],[188,1,1,true,111],[190,0,0,true,99],[190,1,1,true,99],[194,0,0,true,17],[194,1,1,false,137],[196,0,0,true,77],[196,1,1,true,122],[197,0,0,true,109],[197,1,1,true,130],[198,0,1,false,40],[198,1,1,false,113],[213,0,0,true,92],[213,1,1,true,90],[214,0,0,true,188],[214,1,1,true,312],[217,0,0,true,197],[217,1,1,true,196],[221,0,0,true,196],[221,1,1,true,217],[301,0,0,true,45],[301,1,1,true,103],[302,0,0,false,4],[302,1,0,false,302],[310,0,0,true,214],[310,1,1,true,62],[312,0,0,true,11],[312,1,1,true,38]];
const tree=[[["node58",[["node55","node65"],["I","I"]]],[[["node72",[[["node58",["node55","node65"]],["node75",[["node55",["node58","node65"]],[["node70",["node58","node65"]],[["node65","node65"],["node58",[["node55","node65"],["I","I"]]]]]]]],[[[["node49","I"],"node65"],[["node55","node65"],["I","I"]]],[["node49","I"],"node65"]]]],["node58","node65"]],[[["node58",["node70",["node65",["I","I"]]]],[[["node55","node65"],["I","I"]],["node58",[["node55","node65"],["I","I"]]]]],[[["node70",["node65",["I","I"]]],"node65"],["node58",[["node55","node65"],"I"]]]]]],[[["node58",["node70",["node65",["I","I"]]]],["I",[[["node70",[["node55","node65"],"I"]],[["node65","node65"],["node58",[["node55","node65"],["I","I"]]]]],"I"]]],[["node70",["node58","node65"]],[[[[["I",[[["node70",[["node55","node65"],"I"]],[["node65","node65"],["node58",[["node55","node65"],["I","I"]]]]],"I"]],[[[["node49","I"],"node65"],[["node55","node65"],["I","I"]]],[["node49","I"],"node65"]]],[[["node70",[["node55","node65"],"I"]],"I"],[["node70",["node58","node65"]],[[["node55","node65"],["I","I"]],["node58",[["node55","node65"],["I","I"]]]]]]],[[["node65","node65"],[[["node70",["node70",[[["node70",["node65",["I","I"]]],"node65"],["node58",[["node55","node65"],"I"]]]]],["node58",[["node55","node65"],"I"]]],[[["node70",["node65",["I","I"]]],"node65"],["node58",[["node55","node65"],"I"]]]]],[[["node70",["node70",[["node55","node65"],"I"]]],[[["node65","node65"],["node70",[["node55","node65"],"I"]]],[[["node70",["node65",[[["node49","I"],"node65"],"node65"]]],[[[["node49","I"],"node65"],[["node55","node65"],["I","I"]]],[[["node70",["node70",[["node55","node65"],"I"]]],["node65",[[["node49","I"],"node65"],"node65"]]],[["node70",["node65",["I","I"]]],"node65"]]]],[["node49","I"],"node65"]]]],"node142"]]],["node150","X"]]]]];
const m=engine(fixed);
let best=tree,bestc=m.cost(best),cur=best,curc=bestc,iter=0,accepted=0;
let seed=123452456;const rng=()=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;};
let improvements=[];
while(iter<7438){
 let ps=m.paths(cur),p=ps[Math.floor(rng()*ps.length)],n=m.get(cur,p),right=rng()<.5;
 if(!Array.isArray(n[right?0:1]))continue;
 let nt=m.rotate(cur,p,right),nc=m.cost(nt),temp=0.18+(iter%1600)/1600*.2;
 if(nc.n<curc.n||(nc.n<=bestc.n+3&&rng()<Math.exp((curc.n-nc.n)/temp))){cur=nt;curc=nc;accepted++;}
 if(nc.n<bestc.n){best=nt;bestc=nc;improvements.push({iter,n:nc.n,raw:nc.raw,pairs:nc.pairs.length});if(nc.n<194)break;}
 if(++iter%1600===0){cur=best;curc=bestc;}
}
console.log(JSON.stringify({iter,accepted,best:bestc.n,raw:bestc.raw,improvements,seed:123452456,scope:"Finite occurrence-rotation scoring search; intermediate source graphs and physical contracts are not asserted valid."},null,2));
