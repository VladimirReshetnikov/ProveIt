#!/usr/bin/env python3
"""Fuse MP's pushD;imply arithmetic, preserving the source-level output."""
import inverse_mp as q,json
s,b,z=q.s,q.b,q.z
OUT=q.W/'fused_forward_mp';OUT.mkdir(exist_ok=True)
move17=q.CD(1),(q.CI(7),q.CC(2))
copyD=q.get(4671,4678)
pairscale=q.get(4689,4705)
move76=q.get(4614,4617)
results=[]
for k,n in enumerate(q.assocs((move17,copyD,move76,pairscale))):
 for a in range(9):
  for d in range(9):
   rr=[3,a,7,0,d,5,0,0,11]
   out,st=q.sim(n,rr)
   exp=rr.copy();exp[1]=4*((a+d)*(a+d+1)//2+d)
   assert out==exp,(a,d,out,exp)
 tt=s.replace(q.TREE,'111100',n);rr=s.sites(tt)
 assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 rec={'variant':k,'source_metrics':s.metrics(tt),'small_cases':81,'semantics':'I(TW,D) computed preserving WS,D and clearing scratches; needs symbolic macro proof'}
 od=OUT/f'v{k}';od.mkdir(exist_ok=True);(od/'sites.json').write_bytes(s.compact(rr))
 try:
  U,m=z.compile_tree(q.T,q.TREE,tt);rec['compiler']=m;(od/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (od/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print(json.dumps(rec),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
