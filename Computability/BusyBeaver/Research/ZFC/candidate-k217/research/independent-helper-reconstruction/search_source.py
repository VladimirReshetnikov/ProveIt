"""Bounded explicit helper-span reassociation. Never changes primitive word.
Target helper is ((subtree104,X),subtree90). Only closed maximal interval
fragments are spliced; both complete CFG resolvers must accept every variant.
"""
from pathlib import Path
from functools import cache
import json,hashlib,time
import source_language as s
import source_splice as sp
O=Path(__file__).parent
A=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20')
source=A/'source/sites218.json';oldrows=json.loads(source.read_text());old=s.tree(oldrows);word=[x[1:]for x in oldrows];cfg=s.graph_intervals(oldrows);assert cfg==s.graph_arithmetic(oldrows)[0]
roles=json.loads(Path('/tmp/zfc-intake191-physical-comparison/roles.json').read_text())['roles']
A0=s.subtree(old,roles['104']['prefixes'][0]);C0=s.subtree(old,roles['90']['prefixes'][0]);S31=s.subtree(old,roles['31']['prefixes'][0]);assert s.boundary(A0)==s.boundary(C0)==(0,0,False)
spans=[]
def walk(n,p='',i=0):
 j=i+sp.size(n);spans.append((n,p,i,j))
 if not s.leaf(n):walk(n[0],p+'0',i);walk(n[1],p+'1',i+sp.size(n[0]))
walk(old)
starts=[(n,p,i,j)for n,p,i,j in spans if n==A0 and p.startswith('11101001001')]
ends=[(n,p,i,j)for n,p,i,j in spans if n==C0]
def assoc(xs,kind):
 if len(xs)==1:return xs[0]
 k=1 if kind=='right'else len(xs)-1 if kind=='left'else len(xs)//2
 return assoc(xs[:k],kind),assoc(xs[k:],kind)
seen=set();results=[];rejected=[];begun=time.monotonic()
for _,pa,lo,ae in starts:
 for _,pc,cs,hi in ends:
  if not ae<cs or hi-lo>600:continue
  try:middle=sp.closed_forest(old,ae,cs)
  except AssertionError as e:rejected.append({'span':[lo,hi],'stage':'middle_closed','reason':str(e)});continue
  for kind in('right','left','balanced'):
   X=assoc(middle,kind)
   # Avoid using the exact deleted400 role as the necessary unchanged helper leg.
   if X==S31:continue
   H=((A0,X),C0)
   try:new=sp.apply_closed_splices(old,{(lo,hi):H})
   except AssertionError as e:rejected.append({'span':[lo,hi],'association':kind,'stage':'splice','reason':str(e)});continue
   if new in seen:continue
   seen.add(new);rows=s.sites(new);assert[x[1:]for x in rows]==word
   g=s.graph_intervals(rows);assert g==cfg and s.graph_arithmetic(rows)[0]==g
   oldoutside={p:(o,r)for p,o,r in oldrows if not p.startswith('11101001001')};newmap={p:(o,r)for p,o,r in rows};assert all(newmap.get(p)==v for p,v in oldoutside.items())
   k=len(results);p=O/f'candidate{k:03d}.sites.json';p.write_bytes(s.compact(rows))
   item={'id':k,'span':[lo,hi],'left104':pa,'right90':pc,'middle_factors':len(middle),'association':kind,'metrics':s.metrics(new),'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'complete_word_CFG_outside_AX':True,'helper_type':hashlib.sha256(s.compact(H)).hexdigest(),'helper_left_type':hashlib.sha256(s.compact(H[0])).hexdigest()};results.append(item)
   assert time.monotonic()-begun<90
out={'status':'BOUNDED_EXACT_HELPER_SPAN_REASSOCIATION_COMPLETE','elapsed_seconds':time.monotonic()-begun,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'family':{'starts':'two in-AX occurrences of closed subtree104','ends':'later closed subtree90, total span at most600leaves','middle':'maximal original closed fragments; right/left/balanced only','exclude':'X exactly equals subtree31, which would reuse the overwritten69/400 branch in the gadget'},'results':results,'rejected':rejected,'promising':[r['id']for r in results if r['metrics']['dag_nodes']<=204 and r['metrics']['maximum_zero_run']<=6],'scope':'Exact source equivalence only. No physical allocation, runtime, or blank startup.'}
(O/'source-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('results','rejected')},indent=2));print('best',json.dumps(sorted(results,key=lambda r:(r['metrics']['dag_nodes'],r['metrics']['maximum_zero_run']))[:8],indent=2))
