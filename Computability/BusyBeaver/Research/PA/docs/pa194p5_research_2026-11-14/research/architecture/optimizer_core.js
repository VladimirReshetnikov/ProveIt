
const MAC={node65:90,node55:98,node58:12,node70:166,node49:19,node72:69,node75:213,node142:194,node150:221,node60:99,node61:190};
const REVMAC=Object.fromEntries(Object.entries(MAC).map(([k,v])=>[v,k]));
let NS=[],IX=new Map(),ATTR={};
for(const line of load("attrs").split("\n").slice(1)){const v=line.trim().split(/\s+/).map(Number);if(v.length===6)ATTR[v[0]]={h:v[1],l:v[2],m:v[3],mi:v[4],inc:v[5],len:1,bad:0};}
ATTR[-2]=ATTR[-1];ATTR[17]={...ATTR[-1]};ATTR[144]={...ATTR[-1]};
function leaf(q){return -q-10000;}function physical(x){return -x-10000;}
function at(x){return x<0?ATTR[physical(x)]:NS[x].a;}
function pair(l,r){let key=l+","+r;if(IX.has(key))return IX.get(key);let a=at(l),b=at(r),v={h:1+Math.max(a.h,b.h),l:a.l+1,m:Math.max(a.l+1,a.m,b.m),mi:Math.max(a.mi,b.mi,a.inc?1+a.l:0),inc:a.inc,len:a.len+b.len,bad:a.bad+b.bad+((l<0&&physical(l)===194)?1:0)+((r<0&&physical(r)===69)?1:0)};let id=NS.length;NS.push({l,r,a:v});IX.set(key,id);return id;}
function loadg(g){let memo={};function go(x){if(Array.isArray(x)){if(x[0]==="leaf"){let q=x[1]==="inc"?61:x[1]==="dec"?(x[2]===3?17:144):-1;return leaf(q);}return pair(go(x[0]),go(x[1]));}if(MAC[x]!==undefined)return leaf(MAC[x]);if(memo[x]!==undefined)return memo[x];let v=g.rules[x];return memo[x]=pair(go(v[0]),go(v[1]));}return go(g.root);}
function reaches(root){let seen=new Set(),arr=[];function go(t){if(t<0||seen.has(t))return;seen.add(t);arr.push(t);go(NS[t].l);go(NS[t].r);}go(root);return arr;}
function replace(root,old,fresh){let memo=new Map();function go(t){if(t===old)return fresh;if(t<0)return t;if(memo.has(t))return memo.get(t);let n=NS[t],id=pair(go(n.l),go(n.r));memo.set(t,id);return id;}return go(root);}
function exportg(root){let rules={};const term=x=>x>=0?"g"+x:(physical(x)===61?["leaf","inc",1]:physical(x)===-1?["leaf","breakTo",1]:physical(x)===17?["leaf","dec",3]:physical(x)===144?["leaf","dec",4]:REVMAC[physical(x)]);for(const id of reaches(root))rules["g"+id]=[term(NS[id].l),term(NS[id].r)];return {root:"g"+root,rules};}
const dense=load("main-data-0").value.structuredContent.content.trim().split("\n").map(s=>s.split(" "));
const labels=JSON.parse(load("main-data-1").value.structuredContent.content);
let BASE={};for(const [q,b,w,d,n]of dense){const qq=labels[+q];if(qq<1300){BASE[qq]??=[];BASE[qq][+b]=[+w,d==="R"?1:0,labels[+n]];}}
const EQ=(a,b)=>a&&b&&a[0]===b[0]&&a[1]===b[1]&&a[2]===b[2];
function compile(root){let rows=Object.fromEntries(Object.entries(BASE).map(([q,v])=>[q,v.map(a=>a.slice())])),idx=new Map(),intern=new Map(),count=0;function go(x){if(x<0)return physical(x);if(idx.has(x))return idx.get(x);let nn=NS[x],l=go(nn.l),r=go(nn.r);if(l===61&&r===61)return 99;if(l===99&&r===99)return 190;let key=l+","+r;if(intern.has(key))return intern.get(key);let q=2000+count++;idx.set(x,q);intern.set(key,q);rows[q]=[l===-1?[0,0,302]:[0,1,l],r===-1?[0,0,302]:[1,1,r]];return q;}rows[101][1]=[1,1,go(root)];return {rows,count};}
function calc(root,exact=false){let{rows,count:n}=compile(root),inc=new Uint8Array(n),providers=[new Map(),new Map()];
for(const [qs,v]of Object.entries(rows)){for(let b=0;b<2;b++){let a=v[b];if(a[1]&&a[0]===b&&a[2]>=2000)inc[a[2]-2000]|=1<<b;}}
for(const [qs,v]of Object.entries(rows)){if(v[0][0]||v[1][0]!==1||!v[0][1]||!v[1][1]||!rows[v[0][2]]||!rows[v[1][2]])continue;for(let b=0;b<2;b++){let key=rows[v[0][2]][b].join(",")+"|"+rows[v[1][2]][b].join(",");if(!providers[b].has(key))providers[b].set(key,[]);providers[b].get(key).push([+qs,v[0][2],v[1][2]]);}}
let left=[],right=[],ops=[],edges={};for(let j=0;j<n;j++){if(inc[j]===1)left.push(j+2000);if(inc[j]===2)right.push(j+2000);}
for(const a of left)for(const b of right){let choices=[];for(let bit=0;bit<2;bit++){if(EQ(rows[a][bit],rows[b][bit])){choices.push([rows[a][bit]]);continue;}let key=rows[a][bit].join(",")+"|"+rows[b][bit].join(","),pr=providers[bit].get(key)||[];let oo=pr.filter(v=>!v.includes(a)&&!v.includes(b)).map(v=>[bit,0,v[0]]);choices.push(oo);if(!oo.length)break;}if(choices.length===2&&choices.every(v=>v.length)){ops.push({a,b,choices});edges[a]??=[];edges[a].push(b);}}
let mat={},fold=0;function aug(a,seen){for(const b of edges[a]||[]){if(seen.has(b))continue;seen.add(b);if(mat[b]===undefined||aug(mat[b],seen)){mat[b]=a;return true;}}return false;}
for(const a of left)if(aug(a,new Set()))fold++;
let a=at(root),pen=4*a.bad+4*Math.max(a.m-6,0)+4*Math.max(a.mi-5,0)+Math.max(a.h-38,0);
return {n,fold,eff:n-fold,score:n-fold+pen,pen,ops,rows,inc:Array.from(inc)};}
function localvalid(rows,chosen){let alias={},patch={};for(const c of chosen){alias[c.a]=c.b;patch[c.b]=c.actions;}const al=q=>alias[q]??q;for(const c of chosen)for(let h=0;h<2;h++)for(let bit=0;bit<2;bit++){let old=h?c.b:c.a,target=rows[old][bit],q=c.b,pos=0,tape=[h,bit],pass=false;for(let s=0;s<24;s++){if(s&&q===al(target[2])&&pos===(target[1]?1:-1)&&tape[0]===h&&tape[1]===target[0]){pass=true;break;}if(pos< -1||pos>0||alias[q]!==undefined||!rows[q])break;let a=(patch[q]??rows[q])[tape[pos+1]];tape[pos+1]=a[0];pos+=a[1]?1:-1;q=al(a[2]);}if(!pass)return false;}return true;}
function compatible(v){const ops=v.ops;let chosen=[],used=new Set();for(let goal=v.fold;goal>0;goal--){function dfs(i){if(chosen.length===goal)return localvalid(v.rows,chosen)?chosen.slice():null;if(i===ops.length||chosen.length+ops.length-i<goal)return null;let o=ops[i];if(!used.has(o.a)&&!used.has(o.b)){used.add(o.a);used.add(o.b);for(let z of o.choices[0])for(let u of o.choices[1]){chosen.push({a:o.a,b:o.b,actions:[z,u]});let ans=dfs(i+1);if(ans)return ans;chosen.pop();}used.delete(o.a);used.delete(o.b);}return dfs(i+1);}let ans=dfs(0);if(ans)return ans;}return [];}

