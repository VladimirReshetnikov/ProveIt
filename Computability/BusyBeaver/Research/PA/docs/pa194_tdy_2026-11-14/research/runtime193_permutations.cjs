#!/usr/bin/env node
"use strict";
/* Exhaustive finite-family obstruction: 193 runtime core + all physical
   register permutations fixing slot 6, native blank start 74.
   Every prefix ends in a certified rightward writing ray.
   This is not a lower bound on PA-consistency machine state count. */
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {parseTable,tableText}=require("../verification/verify_tdy.cjs");
const BASE=path.resolve(__dirname,"..");
const primaryText=fs.readFileSync(path.join(BASE,"reference/primary.native.tm"),"utf8");
const hash=s=>crypto.createHash("sha256").update(s).digest("hex");
if(hash(primaryText)!=="e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54")throw Error("primary hash");
const primary=parseTable(primaryText);
const SK=[51,36,25,48,32,33,22,55,60];
const BOX=new Set([0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198]);
function eq(a,b){return JSON.stringify(a)===JSON.stringify(b);}
function coreFor(perm){
 const rows={};
 for(const[k,act]of Object.entries(primary)){
  const tr=act.slice(),q=+k.split(",")[0],r=SK.indexOf(tr[2]);
  if(!BOX.has(q)&&r>=0)tr[2]=SK[perm[r]];
  rows[k]=tr;
 }
 delete rows["301,0"];delete rows["301,1"];
 for(const tr of Object.values(rows))if(tr[2]===301)tr[2]=88;
 rows["88,0"]=[0,-1,51];rows["51,0"]=[0,1,122];
 const rayRows={"51,0":[0,1,122],"122,0":[0,-1,137],"137,0":[0,1,30],
  "30,0":[0,1,45],"45,0":[0,1,24],"24,0":[0,-1,35],"35,0":[1,1,35]};
 for(const[k,tr]of Object.entries(rayRows))if(!eq(rows[k],tr))throw Error("ray row "+k);
 return rows;
}
function* permutations(a){if(a.length===0){yield [];return;}for(let i=0;i<a.length;i++)for(const p of permutations([...a.slice(0,i),...a.slice(i+1)]))yield[a[i],...p];}
const slots=[0,1,2,3,4,5,7,8],identity=[0,1,2,3,4,5,6,7,8];
const identityCore=coreFor(identity);
const coreText=tableText(identityCore);
// Uniform proof certificate for all 9! layouts, not just the enumerated subset.
const routingKeys=new Set(Object.entries(primary).filter(([k,tr])=>!BOX.has(+k.split(",")[0])&&SK.includes(tr[2])).map(([k])=>k));
let uq=74,uh=0,uones=new Set();const commonPrefix=[];
for(let st=0;st<78;st++){
 const bit=+uones.has(uh),key=uq+","+bit;
 if(routingKeys.has(key))throw Error("prefix depends on layout at step "+st);
 const[w,d,n]=identityCore[key];commonPrefix.push({time:st,state:uq,head:uh,read:bit,one_cells:[...uones].sort((a,b)=>a-b),transition:[w,d,n]});
 if(w)uones.add(uh);else uones.delete(uh);uh+=d;uq=n;
}
if(uq!==45||uh!==4||!eq([...uones].sort((a,b)=>a-b),[-3,1,4]))throw Error("uniform prefix endpoint");
if(!routingKeys.has("45,1")||primary["45,1"][2]!==SK[7])throw Error("first route is physical slot 7");
for(let r=1;r<9;r++)if(!eq(identityCore[SK[r]+",0"],[0,1,SK[r-1]]))throw Error("skip-chain recurrence");
const nineCases=[];
for(let r=0;r<9;r++){
 let q=SK[r],h=5,ones=new Set([-3,1]);
 for(let t=0;t<r+6;t++){
  const[w,d,n]=identityCore[q+","+(+ones.has(h))];if(w)ones.add(h);else ones.delete(h);h+=d;q=n;
 }
 if(q!==35||h!==7+r||!eq([...ones].sort((a,b)=>a-b),[-3,1]))throw Error("uniform ray case "+r);
 nineCases.push({selected_slot:r,state51_time:79+r,state51_head:5+r,state35_time:85+r,state35_head:7+r,one_cells:[-3,1]});
}
const allLayouts={layouts_covered:362880,common_prefix_steps:78,common_prefix:commonPrefix,
 prefix_endpoint:{time:78,state:45,head:4,one_cells:[-3,1,4]},first_layout_route:{state:45,read:1,original_slot:7},
 cases:nineCases,conclusion:"Every permutation of all nine physical slots reaches the state-35 rightward writing ray from native blank start 74.",
 method:"One layout-independent finite prefix, the skip-chain recurrence, and nine literal suffix cases. The 9! layouts are covered symbolically, not individually enumerated."};
fs.writeFileSync(path.join(__dirname,"runtime193_all_layouts_certificate.json"),JSON.stringify(allLayouts,null,2)+"\n");
fs.writeFileSync(path.join(__dirname,"runtime193_rejected.native.tm"),coreText);
const lines=["permutation,steps_to_ray_entry,head,rightmost_one,one_cells"];
let tested=0,totalsteps=0,minsteps=Infinity,maxsteps=0;
const histogram={};
for(const p of permutations(slots)){
 const perm=identity.slice();for(let j=0;j<slots.length;j++)perm[slots[j]]=p[j];
 const rows=coreFor(perm);let q=74,h=0,ones=new Set(),cert=null;
 for(let st=0;st<150000;st++){
  if(q===51&&!ones.has(h)&&[...ones].every(x=>x<h)){
   cert={steps:st,head:h,rightmost:ones.size?Math.max(...ones):null,ones:[...ones].sort((a,b)=>a-b)};
   break;
  }
  if(q===254)throw Error("unexpected halt");
  const[w,d,n]=rows[q+","+(+ones.has(h))];if(w)ones.add(h);else ones.delete(h);h+=d;q=n;
 }
 if(cert===null)throw Error("unclassified permutation "+perm.join(""));
 tested++;totalsteps+=cert.steps;minsteps=Math.min(minsteps,cert.steps);maxsteps=Math.max(maxsteps,cert.steps);
 histogram[cert.steps]=(histogram[cert.steps]||0)+1;
 lines.push([perm.join(""),cert.steps,cert.head,cert.rightmost,cert.ones.join(";")].join(","));
}
if(tested!==40320||totalsteps!==3336480)throw Error("enumeration regression");
fs.writeFileSync(path.join(__dirname,"runtime193_permutation_prefixes.csv"),lines.join("\n")+"\n");
const receipt={
 family:"Primary PA194 physical layouts, followed by the 301/88 runtime fold",
 fixed_physical_slot:6,permuted_physical_slots:slots,native_start:74,
 permutations:tested,total_literal_prefix_steps:totalsteps,min_prefix_steps:minsteps,max_prefix_steps:maxsteps,
 step_histogram:histogram,certified_rightward_rays:tested,cutoffs:0,halting_prefixes:0,
 primary_native_sha256:hash(primaryText),runtime193_native_sha256:hash(coreText),
 ray_lemma:"At state 51 with the entire suffix from the head blank, six transitions reach state 35 two cells to the right, with its entire right suffix blank; state 35 then writes 1 and moves right forever.",
 uniform_all_layouts_covered:362880,uniform_certificate:"runtime193_all_layouts_certificate.json",
  scope:"The enumerated subset fixes slot 6. A separate uniform prefix certificate covers all 9! layouts. Fixed native start 74; no general state lower bound."
};
fs.writeFileSync(path.join(__dirname,"runtime193_permutation_receipt.json"),JSON.stringify(receipt,null,2)+"\n");
console.log(JSON.stringify(receipt,null,2));
