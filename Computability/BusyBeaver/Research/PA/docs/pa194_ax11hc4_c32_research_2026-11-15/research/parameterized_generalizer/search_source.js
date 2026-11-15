
function toolkit(rawtext, grammar){
 const pairs=[],keys=new Map(),leafnames=[],leafmap=new Map();let nextLeaf=-1;
 function leaf(s){if(leafmap.has(s))return leafmap.get(s);const id=nextLeaf--;leafnames[-id-1]=s;leafmap.set(s,id);return id}
 function node(a,b){const k=a+','+b;if(keys.has(k))return keys.get(k);const id=pairs.length;pairs.push([a,b]);keys.set(k,id);return id}
 const inc=leaf('inc1'),br=leaf('break1');
 const macro=new Map();
 for(const [n,q] of Object.entries({node65:90,node55:98,node58:12,node70:166,node49:19,node72:69,node75:213,node142:194,node150:221}))macro.set(leaf(n),q);
 macro.set(inc,61);macro.set(node(inc,inc),99);macro.set(node(node(inc,inc),node(inc,inc)),190);
 function parse(g){function rec(v){if(Array.isArray(v)){if(v[0]==='leaf')return v[1]==='inc'?inc:br;return node(rec(v[0]),rec(v[1]))}return g.rules[v]?node(...g.rules[v].map(rec)):v==='node60'?node(inc,inc):v==='node61'?node(node(inc,inc),node(inc,inc)):leaf(v)}return rec(g.root)}
 const orig=parse(grammar);
 const fixed=new Map();
 for(const line of rawtext.trim().split('\n')){const [q,b,w,d,n]=line.split(/\s+/);if(+q<1300)fixed.set(+q*2+(+b),[+w,d==='R'?1:0,+n]);}
 const actsig=a=>a.join(',');
 function build(t){
 const rows=new Map(fixed),index=new Map(),shape=new Set();
 function state(t){if(macro.has(t))return macro.get(t);if(index.has(t))return index.get(t);if(t<0)throw Error('leaf '+leafnames[-t-1]);const q=2000+index.size;index.set(t,q);shape.add(q);for(let b=0;b<2;b++){const ch=pairs[t][b];rows.set(q*2+b,ch===br?[0,0,302]:[b,1,state(ch)]);}return q}
 rows.set(203,[1,1,state(t)]);return {rows,index,shape};
 }
 function opportunities(rows,shape){
 const incoming=new Map();for(const [key,a]of rows){const bit=key%2;if(a[1]===1&&a[0]===bit&&shape.has(a[2]))incoming.set(a[2],(incoming.get(a[2])||0)|(1<<bit))}
 const providers=[new Map(),new Map()];
 for(const key of rows.keys()){if(key%2)continue;const h=key/2,a0=rows.get(key),a1=rows.get(key+1);if(a0[0]!==0||a1[0]!==1||a0[1]!==1||a1[1]!==1)continue;for(let b=0;b<2;b++){const x=rows.get(a0[2]*2+b),y=rows.get(a1[2]*2+b);if(!x||!y)continue;const sig=actsig(x)+'|'+actsig(y);if(!providers[b].has(sig))providers[b].set(sig,[]);providers[b].get(sig).push([h,a0[2],a1[2]])}}
 const left=[...shape].filter(q=>incoming.get(q)===1),right=[...shape].filter(q=>incoming.get(q)===2),ops=[];
 for(const a of left)for(const b of right){const opts=[];for(let bit=0;bit<2;bit++){const x=rows.get(a*2+bit),y=rows.get(b*2+bit);opts.push(actsig(x)===actsig(y)?[x]:(providers[bit].get(actsig(x)+'|'+actsig(y))||[]).filter(v=>!v.includes(a)&&!v.includes(b)).map(v=>[bit,0,v[0]]))}
 if(opts.every(v=>v.length))ops.push([a,b,opts])}
 return ops;
 }
 function match(ops){const edges=new Map(),m=new Map();for(const [a,b]of ops){if(!edges.has(a))edges.set(a,[]);edges.get(a).push(b)}
 function augment(a,seen){for(const b of edges.get(a)||[]){if(seen.has(b))continue;seen.add(b);if(!m.has(b)||augment(m.get(b),seen)){m.set(b,a);return true}}return false}
 for(const a of edges.keys())augment(a,new Set());return [...m].map(([b,a])=>[a,b]);
 }
 function score(t,full=false){const b=build(t),ops=opportunities(b.rows,b.shape),m=match(ops);const cost=b.rows.size/2-m.length;return full?{...b,ops,m,cost}:{cost,readers:b.shape.size,folds:m.length}}
 function replace(t,path,v){if(!path.length)return v;const [a,b]=pairs[t];return path[0]?node(a,replace(b,path.slice(1),v)):node(replace(a,path.slice(1),v),b)}
 function word(t){return t<0?[leafnames[-t-1]]:word(pairs[t][0]).concat(word(pairs[t][1]))}
 function json(t){const rules={},memo=new Map();function rec(t){if(t<0)return t===inc?['leaf','inc',1]:t===br?['leaf','breakTo',1]:leafnames[-t-1];if(memo.has(t))return memo.get(t);const n='g'+memo.size;memo.set(t,n);rules[n]=pairs[t].map(rec);return n}return {root:rec(t),rules}}
 function decode(g){return parse(g)}
 return {pairs,keys,leafnames,leafmap,leaf,node,inc,br,macro,orig,fixed,build,opportunities,match,score,replace,word,json,decode};
}

function search(t, seed, limit, threshold){
 let rngstate=seed>>>0;function rnd(){rngstate=(Math.imul(rngstate,1664525)+1013904223)>>>0;return rngstate/4294967296}
 function paths(root){const out=[];function rec(q,path){if(q<0)return;out.push([path,q]);rec(t.pairs[q][0],path.concat(0));rec(t.pairs[q][1],path.concat(1))}rec(root,[]);return out}
 function mutate(root){const list=paths(root),[path,q]=list[Math.floor(rnd()*list.length)],[a,b]=t.pairs[q];let v;if(rnd()<.5&&a>=0){const [a0,a1]=t.pairs[a];v=t.node(a0,t.node(a1,b))}else if(b>=0){const [b0,b1]=t.pairs[b];v=t.node(t.node(a,b0),b1)}else return root;return t.replace(root,path,v)}
 let best=t.decode(load("newgen189")),cur=best,bsc=t.score(best).cost,cs=bsc,winners=[],logs=[],start=Date.now();
 for(let j=0;j<limit;j++){const ne=mutate(cur);const sc=t.score(ne);if(sc.cost<bsc){best=ne;bsc=sc.cost;logs.push({j,...sc,ms:Date.now()-start});}
 const temp=j%4000<3000?.25:.8;
 if(sc.cost<=cs||rnd()<Math.exp((cs-sc.cost)/temp)){cur=ne;cs=sc.cost}
 if(sc.cost<=threshold){winners.push(t.json(ne));break}
 if(j%4000===3999){cur=best;cs=bsc}
 }
 return {best:t.json(best),score:t.score(best),winners,logs,ms:Date.now()-start};
}
const fs=require("fs"),path=require("path");
const dir=__dirname;
const grammarFile=process.argv[4]||"newgen_189.grammar.json";
function load(k){if(k!=="newgen189")throw Error(k);return JSON.parse(fs.readFileSync(path.join(dir,grammarFile),"utf8"));}
const t=toolkit(fs.readFileSync(path.join(dir,"primary.raw.native.tm"),"utf8"),JSON.parse(fs.readFileSync(path.join(dir,"primary.grammar.json"),"utf8")));
const limit=Number(process.argv[2]||15000),seed=Number(process.argv[3]||20261116);
const r=search(t,seed,limit,Number(process.argv[5]||194));
fs.writeFileSync(path.join(dir,"parameterized_generalizer","search_replayed.json"),JSON.stringify({grammarFile,seed,limit,...r},null,2)+"\n");
console.log(JSON.stringify({seed,limit,score:r.score,winners:r.winners.length,logs:r.logs,elapsed_ms:r.ms},null,2));
