#!/usr/bin/env node
/* Local suffix screen only: never a substitute for universal runtime validation.
   Start at native18 on the last bit of1011011, with a sentinel1 atposition-1.
   Search a replacement18/1=(0,L,n) and one other row, looking for the ordinary
   return tail with prefix10 intact and allfour required ones cleared.
   See cc4_two_row_filter.py for the separate universal rejection stage. */
const fs=require('fs'),path=require('path');
const root=__dirname,rows={};
for(const line of fs.readFileSync(path.join(root,'inputs/pa194.native.tm'),'utf8').trim().split('\n')){
 const [q,b,w,d,n]=line.split(/\s+/);(rows[+q]??=[])[+b]=[+w,d==='R'?1:-1,+n];
}
rows[214]=[[0,1,95],[1,1,188]];rows[188]=[[0,1,111],[1,1,312]];
const states=Object.keys(rows).map(Number),K=8,RIGHT=20;
const initial=(1<<(K-1))|(1<<K)|(1<<(K+2))|(1<<(K+3))|(1<<(K+5))|(1<<(K+6));
const want=(1<<(K-1))|(1<<K),goals=new Set([1*64+1+16,1*64+0+16,2*64-1+16]);
const found=[];let trials=0;
function run(first,patch){
 let q=18,h=6,t=initial,seen=new Set(),vis=[];
 for(let steps=0;steps<100;steps++){
  if(steps&&t===want&&goals.has(q*64+h+16))return {hit:true,steps,vis};
  if(h<-K||h>RIGHT||!rows[q])return {hit:false,vis};
  const key=q+','+h+','+t;if(seen.has(key))return {hit:false,vis};seen.add(key);
  const b=(t>>(h+K))&1,isFirst=q===18&&b===1;
  if(!isFirst&&!vis.some(x=>x[0]===q&&x[1]===b))vis.push([q,b]);
  const [w,d,n]=isFirst?first:(patch&&patch[0]===q&&patch[1]===b?patch.slice(2):rows[q][b]);
  t=(t&~(1<<(h+K)))|(w<<(h+K));h+=d;q=n;
 }
 return {hit:false,vis};
}
for(const n of states){
 const first=[0,-1,n],trace=run(first,null);
 for(const [q,b]of trace.vis.slice(0,20))for(const target of states)for(const w of [0,1])for(const d of [-1,1]){
  trials++;const patch=[q,b,w,d,target],result=run(first,patch);
  if(result.hit)found.push({first,patch,steps:result.steps});
 }
}
fs.writeFileSync(path.join(root,'cc4_two_row_candidates.json'),JSON.stringify(found)+'\n');
console.log(JSON.stringify({trials,found:found.length}));
