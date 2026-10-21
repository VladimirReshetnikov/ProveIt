#!/usr/bin/env node
// Exact local search; negative outcomes are bounded research evidence only.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {fileURLToPath} from 'node:url';

function parse(s){const T={};for(const l of s.trim().split("\n")){if(l[0]==="#")continue;const[q,b,w,d,z]=l.split(" ");T[+q*2+(+b)]=[+w,d==="R"?1:-1,+z];}return T;}
function invariant(T,k=3){
 const Q=[...new Set(Object.keys(T).map(x=>Math.floor(+x/2)))],w=2*k+1,n=1<<w,full=n-1;
 const R=new Map(Q.map(q=>[q,new Uint8Array(n)])),work=[];
 for(let m=0;m<n;m++){R.get(0)[m]=1;work.push([0,m]);}
 for(let i=0;i<work.length;i++){
  const[q,m]=work[i],b=(m>>k)&1,[a,d,z]=T[2*q+b];if(!R.has(z))continue;
  const mm=(m&~(1<<k))|(a<<k),base=d===1?mm>>1:(mm<<1)&full,ext=d===1?1<<(w-1):1;
  for(const x of[base,base|ext])if(!R.get(z)[x]){R.get(z)[x]=1;work.push([z,x]);}
 }
 return R;
}

function broad(table){
 const T=parse(table.text),Q=[...new Set(Object.keys(T).map(x=>Math.floor(+x/2)))].sort((a,b)=>a-b),R=invariant(T);
 const cands=[];
 for(const p of Q)for(const q of Q){if(p>=q||p===0)continue;for(const bit of[0,1]){
  if(JSON.stringify(T[2*p+1-bit])!==JSON.stringify(T[2*q+1-bit]))continue;
  const x=T[2*p+bit],y=T[2*q+bit];if(x[0]!==bit||y[0]!==bit||x[1]!==y[1]||x[2]===y[2])continue;
  const dir=x[1],pm=new Set(),qm=new Set();
  for(let m=0;m<128;m++){if(((m>>3)&1)!==bit)continue;if(R.get(p)[m])pm.add((m>>(3-dir))&1);if(R.get(q)[m])qm.add((m>>(3-dir))&1);}
  if(pm.size!==1||qm.size!==1||[...pm][0]===[...qm][0])continue;
  cands.push({p,q,bit,dir,pm:[...pm][0],qm:[...qm][0],A:x[2],B:y[2]});
 }}return {T,Q,R,cands};
}
function proof(T,p,q,mark,goal,replacement,bit,dir){
 const init={[-dir]:mark,[0]:bit},stack=[[p,0,init,init,0]];
 let nodes=0;
 while(stack.length){
  let[s,h,t,o,step]=stack.pop();if(++nodes>200)return "nodes";
  if(step>0&&s===goal&&h===dir&&Object.keys(t).every(k=>t[k]===o[k]))continue;
  if(step>=32)return "steps";if(!T[2*s])return "halt";
  if(t[h]===undefined){if(Object.keys(t).length>=8)return "cells";for(const b of[0,1])stack.push([s,h,{...t,[h]:b},{...o,[h]:b},step]);continue;}
  const b=t[h],r=s===p&&b===bit?replacement:T[2*s+b];
  let[w,d,z]=r;if(z===q)z=p;
  stack.push([z,h+d,{...t,[h]:w},o,step+1]);
 }return "PASS";
}

function search(table,record){
 const T=parse(table.text),Q=[...new Set(Object.keys(T).map(x=>Math.floor(+x/2)))].sort((a,b)=>a-b);
 const result={name:table.name,hits:[],counts:{},tested:0};
 for(const {p,q,pm,qm,A:pz,B:qz,bit,dir}of record.candidates){
  for(const keep of[p,q]){
   const del=keep===p?q:p,km=keep===p?pm:qm,dm=keep===p?qm:pm;
   const kz=keep===p?pz:qz,dz=keep===p?qz:pz;
   for(const write of[0,1])for(const move of[-1,1])for(const target of Q){
    if(target===del)continue;
    result.tested++;const repl=[write,move,target];
    const a=proof(T,keep,del,km,kz===del?keep:kz,repl,bit,dir);result.counts[a]=(result.counts[a]||0)+1;
    if(a!=="PASS")continue;
    const b=proof(T,keep,del,dm,dz===del?keep:dz,repl,bit,dir);result.counts["second_"+b]=(result.counts["second_"+b]||0)+1;
    if(b==="PASS")result.hits.push({keep,del,bit,dir,repl});
   }
  }
 }return result;
}
function synth(table){
 const {T,Q,R,cands}=broad(table),out={name:table.name,hits:[],helper_tests:0};
 for(const{p,q,pm,qm,A,B,bit,dir}of cands){
  const phi=z=>z===q?p:z,eq=(x,y)=>x[0]===y[0]&&x[1]===y[1]&&phi(x[2])===phi(y[2]);
  for(const h of Q){if([p,q].includes(h))continue;out.helper_tests++;const choices=[];
   for(const[mark,dest]of[[pm,A],[qm,B]]){
    const hr=T[2*h+mark];if(hr[0]!==mark||hr[1]!==dir){choices.push([]);continue;}
    const nextbits=new Set();for(let m=0;m<128;m++)if(R.get(h)[m]&&((m>>3)&1)===mark)nextbits.add((m>>(3+dir))&1);
    const oldchild=hr[2],providers=[];
    for(const u of Q){if([p,q,h].includes(u))continue;const ur=T[2*u+bit];
     if(ur[0]!==bit||ur[1]!==dir||phi(ur[2])!==phi(dest))continue;
     if([...nextbits].every(b=>T[2*oldchild+b]&&eq(T[2*u+b],T[2*oldchild+b])))providers.push(u);
    }choices.push(providers);
   }if(choices.every(x=>x.length))out.hits.push({keep:p,del:q,h,pm,qm,A,B,bit,dir,providers:choices});
  }
 }return out;
}

const here=path.dirname(fileURLToPath(import.meta.url));
const index=JSON.parse(fs.readFileSync(path.join(here,"table_index.json"),"utf8"));
index.push({name:"FM215",file:"fm215.native.tm"});
const result={status:"BOUNDED_SEARCH_COMPLETE_NO_HITS",
 scope:"Both symbols and move directions; opposite one-bit origin markers from the radius-three all-tape invariant. One retained state row plus incoming redirects, or three-step marker with helper resynthesis preserving every old helper step in two steps. Bounds do not establish impossibility outside the searched families.",
 bounds:{radius:3,execution_steps:32,visited_cells:8,symbolic_nodes:200},
 tables:[],total_pairs:0,total_row_candidates:0,total_helper_tests:0};
for(const item of index){
 const raw=fs.readFileSync(path.join(here,item.file));
 const table={name:item.name,text:raw.toString("utf8")};
 const record={name:item.name,candidates:broad(table).cands};
 const row_search=search(table,record),helper_search=synth(table);
 result.tables.push({...item,sha256:crypto.createHash("sha256").update(raw).digest("hex"),
   marker_pairs:record.candidates,row_search,helper_search});
 result.total_pairs+=record.candidates.length;
 result.total_row_candidates+=row_search.tested;
 result.total_helper_tests+=helper_search.helper_tests;
 if(row_search.hits.length||helper_search.hits.length)result.status="HITS_REQUIRE_INDEPENDENT_REVIEW";
 process.stdout.write(item.name+": "+record.candidates.length+" marker pairs, "+row_search.tested+" row candidates, "+helper_search.helper_tests+" helper tests\n");
}
const output=process.argv[2]||path.join(here,"marker_search_results.json");
fs.writeFileSync(output,JSON.stringify(result,null,2)+"\n");
process.stdout.write(JSON.stringify({status:result.status,total_pairs:result.total_pairs,total_row_candidates:result.total_row_candidates,total_helper_tests:result.total_helper_tests})+"\n");
