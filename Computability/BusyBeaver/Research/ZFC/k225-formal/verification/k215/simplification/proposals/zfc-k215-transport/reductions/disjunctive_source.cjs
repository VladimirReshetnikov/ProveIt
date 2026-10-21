#!/usr/bin/env node
// Complete disjunctive source abstraction and a measured dead-loop splice.
// This is a finite ordinary checker, not a proof-assistant theorem.
const fs=require('node:fs'),crypto=require('node:crypto'),path=require('node:path');
const src=process.argv[2]||path.join(__dirname,'sites215.json');
const out=process.argv[3]||path.join(__dirname,'source_abstraction.json');
const raw=fs.readFileSync(src),rows=JSON.parse(raw),expected='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba';
function requireThat(c,m){if(!c)throw Error(m);}
requireThat(crypto.createHash('sha256').update(raw).digest('hex')===expected,'pinned source bytes');
function cfg(rows){const n=rows.length,ix=new Map(rows.map((r,i)=>[r[0],i])),inter=new Map();
 function visit(p){if(ix.has(p)){let i=ix.get(p);inter.set(p,[i,i+1]);return[i,i+1];}let a=visit(p+'0'),b=visit(p+'1');requireThat(a[1]===b[0],'noncontiguous tree');inter.set(p,[a[0],b[1]]);return[a[0],b[1]];}visit('');
 function unwind(p,bit,k){while(p.length){let last=p[p.length-1];p=p.slice(0,-1);if(last===bit&&!--k)return inter.get(p)[bit==='0'?1:0]%n;}return 0;}
 return rows.map(([p,op,r],i)=>op==='CI'?[(i+1)%n]:op==='CD'?[unwind(p,'0',1),(i+1)%n]:op==='CB'?[unwind(p,'0',r)]:op==='CC'?[unwind(p,'1',r)]:[]);}
const g=cfg(rows),n=rows.length,base=3**9,P=Array.from({length:9},(_,i)=>3**i);
const seen=new Uint32Array(Math.ceil(n*base/32)),queue=[],masks=Array.from({length:n},()=>Array(9).fill(0));let head=0;
function add(pc,v){const k=pc*base+v,w=k>>>5,b=1<<(k&31);if(seen[w]&b)return;seen[w]|=b;queue.push(k);}
add(0,2); // exact initial registers (4,0,0,0,0,0,0,0,0) abstract to (large,0,...,0).
const began=Date.now();
while(head<queue.length){const k=queue[head++],pc=Math.floor(k/base),v=k%base,[,op,r]=rows[pc];
 let rem=v;for(let j=0;j<9;j++){masks[pc][j]|=1<<(rem%3);rem=Math.floor(rem/3);}
 if(op==='CH')continue;
 if(op!=='CI'&&op!=='CD'){add(g[pc][0],v);continue;}
 const x=Math.floor(v/P[r])%3;
 if(op==='CI'){add(g[pc][0],v+(x<2?P[r]:0));continue;}
 if(x===0){add(g[pc][0],v);continue;}
 add(g[pc][1],v-P[r]);if(x===2)add(g[pc][1],v);
}
const unreachable=rows.map((_,i)=>i).filter(i=>!masks[i][0]),zero=rows.map((_,i)=>i).filter(i=>rows[i][1]==='CD'&&masks[i][rows[i][2]]===1);
requireThat(JSON.stringify(unreachable)==='[4672,4673,4734]','unreachable census changed');
requireThat(JSON.stringify(zero)==='[4671,4733]','zero-decrement census changed');
const leaf=t=>typeof t[0]==='string',byp=new Map(rows.map(r=>[r[0],[r[1],r[2]]]));
function tree(p=''){return byp.has(p)?byp.get(p):[tree(p+'0'),tree(p+'1')];}
function at(t,p){return p.length?at(t[+p[0]],p.slice(1)):t;}
function replace(t,p,x){if(!p.length)return x;let r=[...t];r[+p[0]]=replace(r[+p[0]],p.slice(1),x);return r;}
function walk(t,p='',out=[]){if(leaf(t))out.push([p,...t]);else{walk(t[0],p+'0',out);walk(t[1],p+'1',out);}return out;}
function metrics(t){let distinct=new Set(),leaves=0,depth=0,zeroRun=0;
 function go(x,p){distinct.add(JSON.stringify(x));if(leaf(x)){leaves++;depth=Math.max(depth,p.length);zeroRun=Math.max(zeroRun,...p.split('1').map(s=>s.length));}else{go(x[0],p+'0');go(x[1],p+'1');}}go(t,'');
 return{dag_nodes:distinct.size,primitive_occurrences:leaves,maximum_depth:depth,maximum_zero_run:zeroRun};}
const t=tree(),p1='110100101110',p2='11110011',r1=replace(t,p1,at(t,p1)[1]),r2=replace(t,p2,at(t,p2)[1]),both=replace(r1,p2,at(t,p2)[1]);
const pruned=walk(both),pg=cfg(pruned),gone=new Set([4671,4672,4673,4733,4734]),retained=rows.map((_,i)=>i).filter(i=>!gone.has(i)),newpos=new Map(retained.map((i,j)=>[i,j]));
function skip(i){if(i===4671)return 4674;if(i===4733)return 4735;return i;}
let checkedEdges=0;
for(let j=0;j<retained.length;j++){const i=retained[j];requireThat(JSON.stringify(rows[i].slice(1))===JSON.stringify(pruned[j].slice(1)),'retained primitive changed');
 const expected=g[i].map(skip).map(i=>newpos.get(i));requireThat(JSON.stringify(expected)===JSON.stringify(pg[j]),'guarded source edge changed');checkedEdges+=expected.length;}
fs.writeFileSync(path.join(path.dirname(out),'pruned-source.json'),JSON.stringify(pruned)+'\n');
const receipt={status:'COMPLETE_DISJUNCTIVE_FIXED_POINT_AND_GUARDED_SPLICE_CHECK',source_sha256:expected,abstract_classes:['zero','one','at_least_two'],abstract_store_count:base,initial_registers:[4,0,0,0,0,0,0,0,0],reachable_abstract_configurations:queue.length,worklist_processed:head,unreachable_ordinals:unreachable,always_zero_decrements:zero,original:metrics(t),delete_first_loop:metrics(r1),delete_second_loop:metrics(r2),delete_both:metrics(both),deleted_ordinals:[...gone],retained_guarded_edges_checked:checkedEdges,seconds:(Date.now()-began)/1000,proof_assistant_checked:false,scope:'Exact finite reachability of the stated saturated abstract machine, an overapproximation of all concrete source runs from the calibrated seed. No new unreachable ordinal beyond the existing product-domain analysis. The five-leaf splice preserves retained opcode/register labels and all guarded targets after skipping two proved zero-decrements. No binary allocation or 214-state machine is supplied.'};
fs.writeFileSync(out,JSON.stringify(receipt,null,2)+'\n');console.log(JSON.stringify(receipt,null,2));
