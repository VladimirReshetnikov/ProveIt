#!/usr/bin/env node
// Self-contained symbolic verifier for PA194N5 and PA194N6.
// Node.js 18+, standard library only. No network or proof assistant needed.
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
const HERE=path.dirname(fileURLToPath(import.meta.url));
const read=n=>fs.readFileSync(path.join(HERE,n),"utf8");
const grammar=JSON.parse(read("reference/pa194.grammar.json"));
function expand(t){if(Array.isArray(t))return t;if(grammar.rules[t])return grammar.rules[t].map(expand);return t;}
const data={
 "programLean_result":{value:{structuredContent:{content:read("reference/Program.lean")}}},
 "primary_tree":expand(grammar.root)
};
const load=k=>data[k];

function sha256(s) {
  const K=[0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
  const rot=(a,n)=>(a>>>n)|(a<<(32-n));
  let a=Array.from(s,c=>c.charCodeAt(0)), len=a.length*8; a.push(128);while(a.length%64!==56)a.push(0);a.push(0,0,0,0,(len>>>24)&255,(len>>>16)&255,(len>>>8)&255,len&255);
  let h=[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  for(let offset=0;offset<a.length;offset+=64){
    const w=new Int32Array(64);for(let i=0;i<16;i++)w[i]=(a[offset+i*4]<<24)|(a[offset+i*4+1]<<16)|(a[offset+i*4+2]<<8)|a[offset+i*4+3];
    for(let i=16;i<64;i++){const s0=rot(w[i-15],7)^rot(w[i-15],18)^(w[i-15]>>>3),s1=rot(w[i-2],17)^rot(w[i-2],19)^(w[i-2]>>>10);w[i]=(w[i-16]+s0+w[i-7]+s1)|0}
    let [a0,b,c,d,e,f,g,j]=h;
    for(let i=0;i<64;i++){let S1=rot(e,6)^rot(e,11)^rot(e,25),ch=(e&f)^(~e&g),t1=(j+S1+ch+K[i]+w[i])|0,S0=rot(a0,2)^rot(a0,13)^rot(a0,22),maj=(a0&b)^(a0&c)^(b&c),t2=(S0+maj)|0;j=g;g=f;f=e;e=(d+t1)|0;d=c;c=b;b=a0;a0=(t1+t2)|0}
    [a0,b,c,d,e,f,g,j].forEach((x,i)=>h[i]=(h[i]+x)|0);
  }
  return h.map(x=>(x>>>0).toString(16).padStart(8,"0")).join("");
}
function parseTable(s){const tab={};for(const line of s.trim().split(/\n/)){let[q,b,w,d,n]=line.trim().split(/\s+/);tab[q+","+b]=[+w,d==="R",+n]}return tab}
function tabText(t){return Object.keys(t).map(k=>k.split(",").map(Number)).sort((a,b)=>a[0]-b[0]||a[1]-b[1]).map(([q,b])=>{let[w,d,n]=t[q+","+b];return q+" "+b+" "+w+" "+(d?"R":"L")+" "+n+"\n"}).join("")}
function dense(t){let qs=[74],ind={74:0};for(const q of qs)for(let b=0;b<2;b++){const n=t[q+","+b][2];if(n!==254&&ind[n]===undefined){ind[n]=qs.length;qs.push(n)}}if(qs.length!==194)throw Error("bad count"+qs.length);const d={};for(let key in t){let[q,b]=key.split(",").map(Number),[w,m,n]=t[key];d[ind[q]+","+b]=[w,m,n===254?194:ind[n]]}return {table:d,labels:qs.concat(254)}}
function startup(t,path){let h=-2,expected=new Set([h-1,h+48]);for(let i=0;i<path.length;i++)if(path[i]==="1")expected.add(h+i);let phys=[0,0,0,0,0,0,2,0,0].concat(Array(26).fill(1)),pos=h+49;for(let v of phys){pos++;for(let z=0;z<=v;z++)expected.add(pos+z);pos+=v+1}let state=74,head=0,ones=new Set();for(let step=1;step<=200000;step++){let[w,d,n]=t[state+","+(ones.has(head)?1:0)];if(w)ones.add(head);else ones.delete(head);state=n;head+=d?1:-1;if(state===254)throw Error("early halt");if(state===84&&head===h&&ones.size===expected.size&&Array.from(ones).every(x=>expected.has(x)))return {steps:step,state,head,one_cells:Array.from(ones).sort((a,b)=>a-b),complete_tape:true}}throw Error("startup failed")}


function readNodes(text){let nodes={};for(let line of text.split("\n")){let m=line.match(/^def (\w+) : Tree := \.node (.*)/);if(!m)continue;const cc=[...m[2].matchAll(/\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b/g)].map(m=>m[3]||["leaf",m[1],m[2]===undefined?null:+m[2]]);if(cc.length!==2)throw Error("nodes "+line);nodes[m[1]]=cc;}return nodes}
function source(k,np){
const nodes=readNodes(load("programLean_result").value.structuredContent.content),ax=load("primary_tree"),inc=["leaf","inc",1];
if(np)nodes.node163=["node6","node54"];
if(k===5)nodes.node61=[[inc,"node60"],"node60"];
else if(k===6)nodes.node61=[[inc,"node60"],[inc,"node60"]];
const sites=[];
function walk(t,p){if(typeof t==="string"){return walk(t==="x67"?ax:nodes[t],p)}if(t[0]==="leaf"){sites.push([p,t[1],t[2]]);return}walk(t[0],p+"0");walk(t[1],p+"1");}
walk("node172","");
const byPath=Object.fromEntries(sites.map((x,i)=>[x[0],i]));
function locate(p){if(byPath[p]!==undefined)return byPath[p];for(let i=0;i<sites.length;i++){const q=sites[i][0];if(q.startsWith(p)||(p.startsWith(q)&&!p.slice(q.length).includes("1")))return i;}throw Error("locate "+p);}
function after(p){const i=p.lastIndexOf("0");if(i<0)throw Error("exit");return locate(p.slice(0,i)+"1");}
function cut(p,b,k){for(let i=p.length-1;i>=0;i--)if(p[i]===b&&! --k)return p.slice(0,i);throw Error("cut "+[p,b,k]);}
const ins=sites.map(([p,op,arg])=>op==="inc"?["inc",arg,after(p)]:op==="dec"?["dec",arg,after(cut(p,"0",1)),after(p)]:op==="breakTo"?["jump",after(cut(p,"0",arg))]:op==="continueTo"?["jump",locate(cut(p,"1",arg))]:["halt"]);
return {sites,ins,nodes};
}
const PHYSICAL=[6,2,0,4,3,7,8,5,1], SK=[51,36,25,48,32,33,22,55,60],SKMAP=Object.fromEntries(SK.map((q,i)=>[q,i]));
const BIT=[["b",0],["b",1]],PLAIN=["x","none",-1];
function frame(p,extra=0,effect=PLAIN){return [84,false,[BIT[1]],Array.from(p,b=>BIT[+b]).concat([["r",0,1,48+extra-p.length],BIT[1],effect])]}
function oracle(q,br,x){let[_,kind,r]=x;if(kind==="none"&&SKMAP[q]!==undefined){r=SKMAP[q];return[r===0?1:3,["x","mark",r],false];}if(kind==="mark"&&r<9){if(q===64)return[40,["x","inc",r],false];if(q===0&&br!==null&&br[0]===r)return br[1]?[97,PLAIN,false]:[40,["x","dec",r],true];}return null;}
function norm(s,left=false){let out=[];for(let xx of s){let x=xx;if(x[0]==="b")x=["r",x[1],0,1];if(x[0]==="r"&&x[2]===0&&x[3]===0)continue;let y=out[out.length-1];if(y&&x[0]==="r"&&y[0]==="r"&&x[1]===y[1])out[out.length-1]=["r",x[1],x[2]+y[2],x[3]+y[3]];else out.push(x);}
if(left&&out.length&&out[out.length-1][0]==="r"&&out[out.length-1][1]===0)out.pop();return out;}
function canonical(s){return[s[0],s[1],norm(s[2],true),norm(s[3])]}
function matches(s,t){return s[0]===t[0]&&s[1]===t[1]&&JSON.stringify(norm(s[2],true))===JSON.stringify(t[2])&&JSON.stringify(norm(s[3]))===JSON.stringify(t[3]);}
function sstep(rows,br,s){
const[q,onl,l,r]=s;
if(onl){if(!l.length)return[[q,false,[],[BIT[0]].concat(r)],false];let x=l[0],tail=l.slice(1);
if(x[0]==="b")return[[q,false,tail,[x].concat(r)],false];
if(x[0]==="r"){let[_,b,a,c]=x,act=rows[q+","+b];if(act&&!act[1]&&act[2]===q)return[[q,true,tail,[["r",act[0],a,c]].concat(r)],false];if(c>0)return[[q,true,[BIT[b],["r",b,a,c-1]].concat(tail),r],false];if(a===0)return[[q,true,tail,r],false];}return null;
}
if(!r.length)return null;let x=r[0],tail=r.slice(1);
if(x[0]==="b"){let act=rows[q+","+x[1]];if(!act)return null;let[w,d,n]=act;return[d?[n,false,[BIT[w]].concat(l),tail]:[n,true,l,[BIT[w]].concat(tail)],true];}
if(x[0]==="r"){let[_,b,a,c]=x,act=rows[q+","+b];if(act&&act[1]&&act[2]===q)return[[q,false,[["r",act[0],a,c]].concat(l),tail],false];if(c>0)return[[q,false,l,[BIT[b],["r",b,a,c-1]].concat(tail)],false];if(a===0)return[[q,false,l,tail],false];return null;}
if(tail.length)return null;
let oc=oracle(q,br,x);if(oc){let[n,x2,extra]=oc;return[[n,true,extra?[BIT[1]].concat(l):l,[x2]],false];}
let act=rows[q+",0"];if(act&&act[0]===0&&!act[1])return[[act[2],true,l,r],true];return null;
}
function validate(rows,src){
let contracts=0,max=0,total=0,trace=[];
for(let i=0;i<src.ins.length;i++){let code=src.ins[i],outs=[];
if(code[0]==="inc"){let[_,r,n]=code;outs.push([null,canonical(frame(src.sites[n][0],0,["x","inc",PHYSICAL[r]]))]);}
else if(code[0]==="dec"){let[_,r,z,p]=code;outs.push([[PHYSICAL[r],true],canonical(frame(src.sites[z][0]))]);outs.push([[PHYSICAL[r],false],canonical(frame(src.sites[p][0],1,["x","dec",PHYSICAL[r]]))]);}
else if(code[0]==="jump")outs.push([null,canonical(frame(src.sites[code[1]][0]))]);else outs.push([null,null]);
for(let[br,target]of outs){let s=frame(src.sites[i][0]),moved=false,success=false;
for(let j=0;j<1024;j++){if(moved&&(target===null?s[0]===254:matches(s,target))){success=true;contracts++;total+=j;max=Math.max(max,j);trace.push(j);break;}let next=sstep(rows,br,s);if(!next)break;s=next[0];moved||=next[1];}
if(!success)return{ok:false,site:i,branch:br,contracts};}}
return {ok:true,contracts,max_steps:max,total_steps:total,durations:trace};}


function foldMachine(raw,folds){let alias=Object.fromEntries(folds.map(x=>[x[0],x[1]])),acts=Object.fromEntries(folds.map(x=>[x[1],x[2]])),child={};for(let key in raw){let[q,b]=key.split(",").map(Number);if(alias[q]!==undefined)continue;let[w,d,n]=acts[q]?acts[q][b]:raw[key];child[key]=[w,d,alias[n]===undefined?n:alias[n]];}return{child,alias}}
function checkFolds(raw,child,alias,folds){let incoming={},cases=[];for(let key in raw){let[q,b]=key.split(",").map(Number),[w,d,n]=raw[key];(incoming[n]??=[]).push([q,b,w,d]);}
for(let[a,b,acts]of folds){if(a===74||b===74)throw Error("foldstart");for(let[q,h]of[[a,0],[b,1]]){if(!incoming[q]?.length||incoming[q].some(row=>row[2]!==h||row[3]!==true))throw Error("incoming"+q);for(let read=0;read<2;read++){let[w,d,n]=raw[q+","+read],expn=alias[n]===undefined?n:alias[n],expp=d?1:-1,expt={"-1":h,0:w},state=b,pos=0,tape={"-1":h,0:read},trace=[],ok=false;for(let ticks=1;ticks<=30;ticks++){if(pos!==-1&&pos!==0)throw Error("outside");let[wr,dr,nn]=child[state+","+tape[pos]];trace.push([state,pos,tape[pos],wr,dr,nn]);tape[pos]=wr;pos+=dr?1:-1;state=nn;if(state===expn&&pos===expp&&tape[-1]===expt[-1]&&tape[0]===expt[0]){cases.push({q,history:h,read,ticks,trace});ok=true;break;}}if(!ok)throw Error("foldfailed");}}}return cases;}


function requireTrue(p,m){if(!p)throw Error(m);}
requireTrue(sha256("abc")==="ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad","SHA self-check");
const expected={
 5:{dense:"b521b1086ad29abdaf213feac2a3d2c0eb1bba7524c36e7f627763aeb2377b09",native:"e5bbe8edd0c9b204b799fb5b8fa1c7c685ad48276de1e58bb71b8154f5f02216",sites:3715,contracts:4816,total:1506840,lo:3695},
 6:{dense:"36da42a81d605ccb8b5edae197c7cde311447bd95b9bf1ab771a3e726a41c6f4",native:"63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a",sites:3776,contracts:4877,total:1531094,lo:3756}
};
const baseline=source(4,false);
requireTrue(baseline.sites.length===3673,"Baseline site count");
const rawParent=parseTable(read("reference/unfolded201.native.tm"));
const folds=JSON.parse(read("reference/pa194.folds.json")).concat([[41,99,[[0,false,30],[1,false,2035]]]]);
const box=[0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198];
const receipts=[];
for(const k of [5,6]){
 const raw=JSON.parse(JSON.stringify(rawParent));
 raw["190,0"]=[0,true,330];raw["190,1"]=[1,true,k===5?99:330];
 raw["330,0"]=[0,true,61];raw["330,1"]=[1,true,99];raw["164,1"]=[1,true,114];
 const {child,alias}=foldMachine(raw,folds),local=checkFolds(raw,child,alias,folds);
 requireTrue(local.length===32,"Fold cases");
 requireTrue(box.every(q=>[0,1].every(b=>JSON.stringify(child[q+","+b])===JSON.stringify(rawParent[q+","+b]))),"Arithmetic-engine rows");
 const nt=tabText(child),dt=dense(child),dd=tabText(dt.table);
 requireTrue(nt===read("machines/pa194n"+k+".native.tm"),"Native table");
 requireTrue(dd===read("machines/pa194n"+k+".tm"),"Dense table");
 requireTrue(sha256(nt)===expected[k].native&&sha256(dd)===expected[k].dense,"Table digests");
 const src=source(k,true),parentSource=source(k,false),lo=expected[k].lo,hi=lo+19;
 const relocate=i=>i<=lo?i:i-19;
 const edges=x=>x[0]==="inc"||x[0]==="dec"?x.slice(2):x[0]==="jump"?x.slice(1):[];
 let incoming=[],outside=0;
 parentSource.ins.forEach((r,pc)=>{
  if(pc>=lo&&pc<hi)return;
  for(let t of edges(r))if(t>=lo&&t<hi)incoming.push([pc,t]);
  const n=r[0]==="inc"||r[0]==="dec"?2:1;
  const projected=r.slice(0,n).concat(r.slice(n).map(relocate));
  requireTrue(JSON.stringify(projected)===JSON.stringify(src.ins[relocate(pc)]),"Source splice at "+pc);
  outside++;
 });
 requireTrue(JSON.stringify(incoming)===JSON.stringify([[lo-6,lo]]),"Unique exterior entry");
 const symbolic=validate(child,src);
 requireTrue(symbolic.ok&&symbolic.contracts===expected[k].contracts&&symbolic.max_steps===499&&symbolic.total_steps===expected[k].total,"Universal symbolic contracts");
 requireTrue(src.sites.length===expected[k].sites,"Source sites");
 const initial=startup(child,src.sites[25][0]);
 requireTrue(initial.steps===58320,"Complete startup");
 receipts.push({
  machine:"PA194N"+k,working_states:194,transition_rows:388,native_start:74,native_halt:254,dense_start:0,dense_halt:194,
  raw_controls:202,fixed_controls:135,reader_controls:67,folds:8,local_cases:32,max_local_duration:Math.max(...local.map(c=>c.ticks)),
  source_sites:src.sites.length,source_outcomes:symbolic.contracts,max_symbolic_steps:symbolic.max_steps,total_symbolic_steps:symbolic.total_steps,
  deleted_source_interval:[lo,hi],unique_external_entry:incoming[0],remaining_source_instructions_checked:outside,
  unchanged_arithmetic_engine_controls:box.length,startup:initial,native_sha256:sha256(nt),dense_sha256:sha256(dd),
  proof_scope:"Exact finite certificates and universal symbolic control simulation using unchanged arithmetic-block lemmas; not a new Lean/Rocq kernel theorem."
 });
}
console.log(JSON.stringify({status:"PASS",machines:receipts},null,2));
