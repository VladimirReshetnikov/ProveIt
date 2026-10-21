#!/usr/bin/env node
// Exact local search; bound exits are inconclusive, not semantic counterexamples.
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


function fullPairs(table){
 const T=parse(table.text),Q=[...new Set(Object.keys(T).map(x=>Math.floor(+x/2)))].sort((a,b)=>a-b),R=invariant(T),pairs=[];
 for(const p of Q)for(const q of Q){if(p>=q||p===0)continue;for(const bit of[0,1]){
  if(JSON.stringify(T[2*p+1-bit])!==JSON.stringify(T[2*q+1-bit]))continue;
  if(JSON.stringify(T[2*p+bit])===JSON.stringify(T[2*q+bit]))continue;
  let common=false,pm=[],qm=[];for(let m=0;m<128;m++)if(((m>>3)&1)===bit){if(R.get(p)[m])pm.push(m);if(R.get(q)[m])qm.push(m);if(R.get(p)[m]&&R.get(q)[m])common=true;}
  if(!common&&pm.length&&qm.length)pairs.push({p,q,bit,pm,qm});
 }}return{T,Q,R,pairs};
}
function fullProof(T,keep,del,bit,mask,oldState,repl){
 const old=T[2*oldState+bit],goal=old[2]===del?keep:old[2],gh=old[1];
 const initial={};for(let h=-3;h<=3;h++)initial[h]=(mask>>(h+3))&1;
 const goalTape={...initial,[0]:old[0]};
 const stack=[[keep,0,initial,goalTape,0]];let nodes=0;
 while(stack.length){
  const[s,h,t,g,step]=stack.pop();if(++nodes>200)return "nodes";
  if(step>0&&s===goal&&h===gh&&Object.keys(t).every(k=>t[k]===g[k]))continue;
  if(step>=32)return "steps";if(!T[2*s])return "halt";
  if(t[h]===undefined){if(Object.keys(t).length>=13)return "cells";for(const b of[0,1])stack.push([s,h,{...t,[h]:b},{...g,[h]:b},step]);continue;}
  const b=t[h],[w,d,z]=s===keep&&b===bit?repl:T[2*s+b];
  stack.push([z===del?keep:z,h+d,{...t,[h]:w},g,step+1]);
 }return"PASS";
}
function fullSearch(table){
 const{T,Q,pairs}=fullPairs(table),res={name:table.name,pair_count:pairs.length,tested:0,first_two_pass:0,counts:{},hits:[]};
 for(const{p,q,bit,pm,qm}of pairs)for(const keep of[p,q]){
  const del=keep===p?q:p,tests=[];
  tests.push([p,pm[0]],[q,qm[0]]);
  for(const[state,ms]of[[p,pm],[q,qm]])for(const mask of ms.slice(1))tests.push([state,mask]);
  for(const write of[0,1])for(const move of[-1,1])for(const target of Q){
   if(target===del)continue;res.tested++;const repl=[write,move,target];let pass=true;
   for(let i=0;i<tests.length;i++){const[state,mask]=tests[i],r=fullProof(T,keep,del,bit,mask,state,repl);
    if(r!=="PASS"){pass=false;res.counts[r]=(res.counts[r]||0)+1;break;}
    if(i===1)res.first_two_pass++;
   }if(pass)res.hits.push({keep,del,bit,repl,windows:tests.length});
  }
 }
 return res;
}

const here=path.dirname(fileURLToPath(import.meta.url));
const index=JSON.parse(fs.readFileSync(path.join(here,"table_index.json"),"utf8"));
index.push({name:"FM215",file:"fm215.native.tm"});
const result={status:"BOUNDED_SEARCH_COMPLETE_NO_HITS",
 scope:"All seven-bit allowed windows from the radius-three all-tape invariant. Delete one state from a pair whose other rows agree, redirect incoming edges and replace the retained state's differing row. The allowed read-bit windows must distinguish the two old controls. Bound exits are inconclusive; this is not an unrestricted no-go theorem.",
 bounds:{radius:3,execution_steps:32,total_inspected_cells:13,symbolic_nodes:200},
 tables:[],total_pairs:0,total_row_candidates:0,first_two_windows_pass:0};
for(const item of index){
 const raw=fs.readFileSync(path.join(here,item.file));
 const table={name:item.name,text:raw.toString("utf8")};
 const pairs=fullPairs(table).pairs, row_search=fullSearch(table);
 result.tables.push({...item,sha256:crypto.createHash("sha256").update(raw).digest("hex"),
   pairs,row_search});
 result.total_pairs+=row_search.pair_count;
 result.total_row_candidates+=row_search.tested;
 result.first_two_windows_pass+=row_search.first_two_pass;
 if(row_search.hits.length)result.status="HITS_REQUIRE_INDEPENDENT_REVIEW";
 process.stdout.write(item.name+": "+row_search.pair_count+" pairs, "+row_search.tested+" row candidates\n");
}
const output=process.argv[2]||path.join(here,"full_window_search_results.json");
fs.writeFileSync(output,JSON.stringify(result,null,2)+"\n");
process.stdout.write(JSON.stringify({status:result.status,total_pairs:result.total_pairs,total_row_candidates:result.total_row_candidates,first_two_windows_pass:result.first_two_windows_pass})+"\n");

