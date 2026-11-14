module.exports=function(inputTable,grammar){

function assert(x,s){if(!x)throw Error(s)}
const fixed={}; for(const ln of inputTable.trim().split('\n')){let [q,b,w,d,n]=ln.split(/\s+/);if(+q<1300){fixed[q]??=[];fixed[q][+b]=[+w,d==='R'?1:0,+n]}}
const macroNames={node65:90,node55:98,node58:12,node70:166,node49:19,node72:69,node75:213,node142:194,node150:221,node60:99,node61:190};
let ns=[],uniq=new Map();const leaves=new Map();
for(const [name,q] of Object.entries(macroNames)){ns[q]={leaf:q,name}}
ns[61]={leaf:61,name:'inc'};ns[302]={leaf:302,name:'break'};ns[99]={leaf:99,name:'node60',a:61,b:61};ns[190]={leaf:190,name:'node61',a:99,b:99};ns.length=303;
function node(a,b){if(a===61&&b===61)return 99;if(a===99&&b===99)return 190;let k=a+','+b;let old=uniq.get(k);if(old!==undefined)return old;let i=ns.length;ns.push({a,b});uniq.set(k,i);return i}
function parse(x){if(Array.isArray(x))return x[1]==='inc'?61:302;if(grammar.rules[x])return node(...grammar.rules[x].map(parse));return macroNames[x]}
let initial=parse(grammar.root);
function evaluate(rt,details=false){
let order=[],seen=new Set();
function visit(x){if(ns[x].leaf!==undefined||seen.has(x))return;seen.add(x);order.push(x);visit(ns[x].a);visit(ns[x].b)}visit(rt);
let rows={...fixed}; function qof(x){return ns[x].leaf!==undefined?ns[x].leaf:3000+x}
for(let x of order){let r=[];for(let b=0;b<2;b++){let y=ns[x][b?'b':'a'];r[b]=y===302?[0,0,302]:[b,1,qof(y)]}rows[3000+x]=r}
rows[101]=[fixed[101][0],[1,1,qof(rt)]];
let shp=new Set(order.map(x=>x+3000)),inc={};for(let[q,rr]of Object.entries(rows))for(let b=0;b<2;b++){let[w,d,n]=rr[b];if(shp.has(n)){inc[n]=(inc[n]??0)|((d===1&&w===b)?1<<b:4)}}
let prov=[new Map(),new Map()];for(let[h,rr]of Object.entries(rows)){let [[w0,d0,u0],[w1,d1,u1]]=rr;if(w0!==0||w1!==1||d0!==1||d1!==1||!rows[u0]||!rows[u1])continue;for(let b=0;b<2;b++){let k=rows[u0][b].join(',')+';'+rows[u1][b].join(',');let a=prov[b].get(k)??[];a.push([+h,u0,u1]);prov[b].set(k,a)}}
let left=[...shp].filter(q=>inc[q]===1),right=[...shp].filter(q=>inc[q]===2),edges=new Map(),ops=new Map();
for(let a of left)for(let b of right){let o=[],ok=true;for(let bit=0;bit<2;bit++){let ra=rows[a][bit],rb=rows[b][bit];if(ra.join(',')===rb.join(',')){o.push([ra]);continue}
let key=ra.join(',')+';'+rb.join(','),opts=[];for(let[h,u,v]of prov[bit].get(key)??[]){if(![h,u,v].includes(a)&&![h,u,v].includes(b))opts.push([bit,0,h])}if(!opts.length){ok=false;break}o.push(opts)}
if(ok){let ar=edges.get(a)??[];ar.push(b);edges.set(a,ar);ops.set(a+','+b,o)}}
let match=new Map();function aug(a,seen2){for(let b of edges.get(a)??[]){if(seen2.has(b))continue;seen2.add(b);if(!match.has(b)||aug(match.get(b),seen2)){match.set(b,a);return true}}return false}
for(let a of left)aug(a,new Set());
return details?{score:order.length-match.size,raw:order.length,folds:match.size,order,rows,matches:[...match].map(([b,a])=>[a,b,ops.get(a+','+b)]),opportunities:[...ops]}:order.length-match.size
}
function positions(rt){let arr=[];function walk(x,path){if(ns[x].a===undefined)return;arr.push([x,path]);walk(ns[x].a,path.concat(0));walk(ns[x].b,path.concat(1))}walk(rt,[]);return arr}
function replace(rt,path,val,k=0){if(k===path.length)return val;let n=ns[rt];return path[k]===0?node(replace(n.a,path,val,k+1),n.b):node(n.a,replace(n.b,path,val,k+1))}
function mutate(rt){let pos=positions(rt);for(let attempt=0;attempt<10;attempt++){let[x,path]=pos[Math.floor(Math.random()*pos.length)],n=ns[x];let lr=Math.random()<.5;if(lr&&ns[n.a].a!==undefined){let l=ns[n.a];return replace(rt,path,node(l.a,node(l.b,n.b)))}if(!lr&&ns[n.b].a!==undefined){let r=ns[n.b];return replace(rt,path,node(node(n.a,r.a),r.b))}}return rt}

return {initial,evaluate,mutate,positions,replace,nodes:ns};
};
