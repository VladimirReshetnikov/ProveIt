#!/usr/bin/env node
"use strict";
/* PA194TDY reconstruction and symbolic source-contract checker.
   JavaScript port of the PA194 packet's compiler.py/symbolic_runtime.py.
   Arithmetic-file operations use the inherited unchanged M6 box contracts.
   This executable is not an end-to-end proof-assistant proof.
*/
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const BASE=path.resolve(__dirname,"..");
function assert(x,msg){if(!x)throw Error(msg);}
function sha(s){return crypto.createHash("sha256").update(s).digest("hex");}
function parseTable(text){
 const rows={};
 for(const line of text.trim().split("\n")){
  if(!line.trim()||line.startsWith("#"))continue;
  const fields=line.trim().split(/\s+/);
  assert(fields.length===5,"five columns required");
  const[q,b,w,d,n]=fields;
  assert([b,w].every(x=>x==="0"||x==="1")&&(d==="L"||d==="R"),"invalid action");
  assert(rows[q+","+b]===undefined,"duplicate row");
  rows[q+","+b]=[+w,d==="R"?1:-1,+n];
 }
 return rows;
}
function tableText(rows){
 return Object.keys(rows).map(k=>k.split(",").map(Number)).sort((a,b)=>a[0]-b[0]||a[1]-b[1]).map(([q,b])=>{
  const[w,d,n]=rows[q+","+b];return `${q} ${b} ${w} ${d===1?"R":"L"} ${n}\n`;
 }).join("");
}
function denseTable(rows){
 const order=[74],index=new Map([[74,0]]);
 for(let i=0;i<order.length;i++)for(let b=0;b<2;b++){
  const n=rows[order[i]+","+b][2];
  if(n!==254&&!index.has(n)){index.set(n,order.length);order.push(n);}
 }
 assert(order.length===194,"194 graph-reachable controls");
 const dense={};
 for(const[k,[w,d,n]]of Object.entries(rows)){const[q,b]=k.split(",").map(Number);dense[index.get(q)+","+b]=[w,d,n===254?194:index.get(n)];}
 return{rows:dense,labels:[...order,254]};
}
function startup(rows,p){
 const head0=-2,expected=new Set([head0-1,head0+48]);
 for(let i=0;i<p.length;i++)if(p[i]==="1")expected.add(head0+i);
 const physical=[0,0,0,0,0,0,2,0,0,...Array(26).fill(1)];
 let pos=head0+49;
 for(const v of physical){pos++;for(let k=0;k<v+1;k++)expected.add(pos+k);pos+=v+1;}
 let q=74,h=0,ones=new Set();
 for(let steps=1;steps<=150000;steps++){
  const[w,d,n]=rows[q+","+(+ones.has(h))];if(w)ones.add(h);else ones.delete(h);h+=d;q=n;
  assert(q!==254,"startup halted");
  if(q===84&&h===head0&&ones.size===expected.size&&[...expected].every(x=>ones.has(x)))
   return{steps,state:q,head:h,source_site:25,one_cells:[...ones].sort((a,b)=>a-b),physical_file:physical,complete_tape_equality:true};
 }
 throw Error("exact clean source frame not reached");
}

const BIT=[["b",0],["b",1]];
const PLAIN=["x","none",-1];
let PHYSICAL=[6,2,0,4,3,7,8,5,1];
const SK=[51,36,25,48,32,33,22,55,60];
function oracle(q,br,x){
 let [_,kind,r]=x;
 if(kind==="none"&&SK.includes(q)) {r=SK.indexOf(q);return [r===0?1:3,["x","mark",r],false];}
 if(kind==="mark"&&r<9){
  if(q===64)return [40,["x","inc",r],false];
  if(q===0&&br!==null&&br[0]===r)return br[1]?[97,PLAIN,false]:[40,["x","dec",r],true];
 }
}
function norm(seg,left=false){
 const out=[];
 for(let x of seg){
  if(x[0]==="b")x=["r",x[1],0,1];
  if(x[0]==="r"&&x[2]===0&&x[3]===0)continue;
  if(out.length&&x[0]==="r"&&out[out.length-1][0]==="r"&&out[out.length-1][1]===x[1]){
   const y=out.pop();out.push(["r",x[1],x[2]+y[2],x[3]+y[3]]);
  }else out.push(x);
 }
 if(left&&out.length&&out[out.length-1][0]==="r"&&out[out.length-1][1]===0)out.pop();
 return out;
}
function canonical(s){return [s[0],s[1],norm(s[2],true),norm(s[3])];}
function eq(s,t){return JSON.stringify(s)===JSON.stringify(t);}
function matches(s,t){return s[0]===t[0]&&s[1]===t[1]&&eq(norm(s[2],true),t[2])&&eq(norm(s[3]),t[3]);}
function frame(p,extra=0,effect=PLAIN){return [84,false,[BIT[1]],[...p.split("").map(b=>BIT[+b]),["r",0,1,48+extra-p.length],BIT[1],effect]];}
function sstep(rows,br,s){
 let [q,onl,l,r]=s;
 if(onl){
  if(!l.length)return [[q,false,[],[BIT[0],...r]],false];
  const x=l[0],tail=l.slice(1);
  if(x[0]==="b")return [[q,false,tail,[x,...r]],false];
  if(x[0]==="r"){
   const [_,b,a,c]=x,act=rows[q+","+b];
   if(act&&act[1]===-1&&act[2]===q)return [[q,true,tail,[["r",act[0],a,c],...r]],false];
   if(c>0)return [[q,true,[BIT[b],["r",b,a,c-1],...tail],r],false];
   if(a===0)return [[q,true,tail,r],false];
  }
  return null;
 }
 if(!r.length)return null;
 const x=r[0],tail=r.slice(1);
 if(x[0]==="b"){
  const act=rows[q+","+x[1]];
  if(!act)return null;
  const [w,d,n]=act;
  return [d===1?[n,false,[BIT[w],...l],tail]:[n,true,l,[BIT[w],...tail]],true];
 }
 if(x[0]==="r"){
  const [_,b,a,c]=x,act=rows[q+","+b];
  if(act&&act[1]===1&&act[2]===q)return [[q,false,[["r",act[0],a,c],...l],tail],false];
  if(c>0)return [[q,false,l,[BIT[b],["r",b,a,c-1],...tail]],false];
  if(a===0)return [[q,false,l,tail],false];
  return null;
 }
 if(tail.length)return null;
 const oc=oracle(q,br,x);
 if(oc){const[n,x2,extra]=oc;return[[n,true,extra?[BIT[1],...l]:l,[x2]],false];}
 const act=rows[q+",0"];
 if(act&&act[0]===0&&act[1]===-1)return [[act[2],true,l,r],true];
 return null;
}
function sourceContracts(sites){
 function locate(p){let i=sites.findIndex(([q])=>q===p);if(i>=0)return i;return sites.findIndex(([q])=>q.startsWith(p)||(p.startsWith(q)&&!p.slice(q.length).includes("1")));}
 function after(p){for(let i=p.length-1;i>=0;i--)if(p[i]==="0")return locate(p.slice(0,i)+"1");throw Error("exit"+p);}
 function cut(p,b,k){for(let i=p.length-1;i>=0;i--)if(p[i]===b&&! --k)return p.slice(0,i);throw Error("cut");}
 const instructions=[],cs=[];
 for(const [i,[p,op,arg]] of sites.entries()){
  let ins;
  if(op==="inc")ins=["inc",arg,after(p)];
  else if(op==="dec")ins=["dec",arg,after(cut(p,"0",1)),after(p)];
  else if(op==="breakTo")ins=["jump",after(cut(p,"0",arg))];
  else if(op==="continueTo")ins=["jump",locate(cut(p,"1",arg))];
  else if(op==="halt")ins=["halt"];
  else throw Error(op);
  instructions.push(ins);
  const st=frame(p);
  if(ins[0]==="inc")cs.push([i,null,st,canonical(frame(sites[ins[2]][0],0,["x","inc",PHYSICAL[arg]]))]);
  else if(ins[0]==="dec"){
   cs.push([i,[PHYSICAL[arg],true],st,canonical(frame(sites[ins[2]][0]))]);
   cs.push([i,[PHYSICAL[arg],false],st,canonical(frame(sites[ins[3]][0],1,["x","dec",PHYSICAL[arg]]))]);
  }else if(ins[0]==="jump")cs.push([i,null,st,canonical(frame(sites[ins[1]][0]))]);
  else cs.push([i,null,st,null]);
 }
 return{instructions,cs};
}
function run(rows,c,fuel=1024,observe=null){
 const [site,br,st,t]=c;let s=st,moved=false;
 for(let k=0;k<fuel;k++){
  if(moved&&(t===null?s[0]===254:matches(s,t)))return k;
  if(observe)observe(s);
  const nxt=sstep(rows,br,s);if(nxt===null)return null;const[m,mv]=nxt;s=m;moved||=mv;
 }
 return null;
}
function validate(rows,cs){
 const lengths=[];
 for(const c of cs){const v=run(rows,c);if(v===null)return {ok:false,failed:[c[0],c[1]],completed:lengths.length};lengths.push(v);}
 return {ok:true,contracts:lengths.length,max_steps:Math.max(...lengths),total_steps:lengths.reduce((a,b)=>a+b,0)};
}

function main(){
 const primaryText=fs.readFileSync(path.join(BASE,"reference/primary.native.tm"),"utf8");
 assert(sha(primaryText)==="e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54","pinned primary table hash");
 const primary=parseTable(primaryText),sites=JSON.parse(fs.readFileSync(path.join(BASE,"source/sites.json"),"utf8"));
 assert(sites.length===3673,"source site count");
 PHYSICAL=[6,2,0,4,3,7,8,5,1];
 const baseCS=sourceContracts(sites),baseline=validate(primary,baseCS.cs);
 const expectedInstructions=JSON.parse(fs.readFileSync(path.join(BASE,"source/instructions.json"),"utf8"));
 assert(eq(baseCS.instructions,expectedInstructions),"frozen complete resolved instruction graph");
 assert(eq(baseline,{ok:true,contracts:4780,max_steps:497,total_steps:1479348}),"baseline symbolic regression");
 const rows=JSON.parse(JSON.stringify(primary));
 const edits=[
  [41,1,[0,1,25],[0,1,48]],[61,1,[0,1,25],[0,1,48]],
  [82,1,[0,1,33],[0,1,25]],[144,1,[0,1,48],[0,1,33]]
 ];
 for(const[q,b,old,next]of edits){assert(eq(rows[q+","+b],old),"patch precondition");rows[q+","+b]=next;}
 const box=[0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198];
 assert(box.every(q=>[0,1].every(b=>eq(primary[q+","+b],rows[q+","+b]))),"unchanged arithmetic-box rows");
 PHYSICAL=[6,3,0,4,5,7,8,2,1];
 const changed=sourceContracts(sites);
 assert(eq(baseCS.instructions,changed.instructions),"complete source instruction identity");
 const symbolic=validate(rows,changed.cs);
 assert(eq(symbolic,baseline),"all arbitrary-register source contracts");
 const blank=startup(rows,sites[25][0]);assert(blank.steps===57594,"startup duration");
 const baseBlank=startup(primary,sites[25][0]);assert(baseBlank.steps===58154,"baseline startup");
 const dense=denseTable(rows),nativeText=tableText(rows),denseText=tableText(dense.rows);
 assert(Object.keys(rows).length===388,"total transition rows");
 assert(sha(nativeText)==="2f6e2342151be7c9f7fb8025f81063525c5d276605d2fa87535a9c7d1498755d","TDY native identity");
 assert(sha(denseText)==="84bfe1368312c7c71c9e4706de7cb65923310e25f8d472997c9c57c5aedd7934","TDY dense identity");
 const receipt={
  name:"PA194TDY",working_states:194,transition_rows:388,native_start:74,native_halt:254,dense_start:0,dense_halt:194,
  source_sites:sites.length,source_graph_identical:true,logical_to_physical:PHYSICAL,
  physical_permutation:[0,1,3,5,4,2,6,7,8],native_edits:edits,
  baseline_symbolic:baseline,symbolic,startup:blank,baseline_startup:baseBlank,
  graph_reachable_working_states:dense.labels.length-1,arithmetic_box_rows_unchanged:true,
  native_sha256:sha(nativeText),dense_sha256:sha(denseText),
  proof_scope:"Ordinary PA finite-trace transport using inherited unchanged arithmetic-box contracts and inherited PA calibration; no new end-to-end kernel-checked endpoint"
 };
 for(const d of ["artifacts","verification"])fs.mkdirSync(path.join(BASE,d),{recursive:true});
 fs.writeFileSync(path.join(BASE,"artifacts/pa194_tdy.native.tm"),nativeText);
 fs.writeFileSync(path.join(BASE,"artifacts/pa194_tdy.tm"),denseText);
 fs.writeFileSync(path.join(BASE,"artifacts/pa194_tdy.labels.json"),JSON.stringify(dense.labels)+"\n");
 fs.writeFileSync(path.join(BASE,"verification/receipt_tdy.json"),JSON.stringify(receipt,null,2)+"\n");
 console.log(JSON.stringify(receipt,null,2));
}
if(require.main===module)main();
module.exports={parseTable,tableText,denseTable,startup,sourceContracts,validate,run,sstep,frame,oracle};
