#!/usr/bin/env python3
"""Compare full primitive-effect CFGs, independently of offset certificates.
Not a Rocq/kernel proof. Only standard-library Python and pinned snapshots.
"""
from validation_guard import ensure_safe_runtime, read_pinned_source, read_pinned_source_bytes
ensure_safe_runtime()

from pathlib import Path
from collections import Counter, deque
from functools import lru_cache
import hashlib,json
import prototype as p
HERE=Path(__file__).resolve().parent

def enumerate_leaves(prog):
 nodes,root=prog; leaves=[]
 def visit(n,path):
  for bit,(op,r) in enumerate(nodes[n]):
   q=path+(bool(bit),)
   if op=='N': visit(r,q)
   else: leaves.append((q,op,r))
 visit(root,())
 return leaves

def flatten(prog):
 leaves=enumerate_leaves(prog)
 primitive=[(q,op,r) for q,op,r in leaves if op in ('I','D','H')]
 ordinal={q:i for i,(q,op,r) in enumerate(primitive)}
 @lru_cache(None)
 def epsilon(path):
  seen=set();steps=0
  while True:
   edge,q=p.site(prog,path);op,r=edge
   if op in ('I','D','H'):return q,steps
   assert q not in seen,('control-only cycle',q)
   seen.add(q);steps+=1
   path=p.brk(r,q) if op=='B' else p.cont(r,q)
 def dest(path):return ordinal[epsilon(path)[0]]
 transitions=[]
 for q,op,r in primitive:
  succ=() if op=='H' else ((dest(p.inc(q)),dest(p.brk(1,q))) if op=='D' else (dest(p.inc(q)),))
  transitions.append((op,r,succ))
 initial=dest(())
 queue=deque([initial]);bfs={initial:0};order=[]
 while queue:
  n=queue.popleft();order.append(n)
  for m in transitions[n][2]:
   if m not in bfs:bfs[m]=len(bfs);queue.append(m)
 canonical=[(op,r,tuple(bfs[m]for m in succ))for n in order for op,r,succ in [transitions[n]]]
 return dict(leaves=leaves,primitive=primitive,transitions=transitions,initial=initial,bfs=bfs,canonical=canonical,
             epsilon_queries=epsilon.cache_info().misses)

def main():
 a=flatten(p.read_prog('Prog215.v'));b=flatten(p.read_prog('DagPerm.v'))
 effects_a=[(op,r)for _,op,r in a['primitive']];effects_b=[(op,r)for _,op,r in b['primitive']]
 diffs=[{'ordinal':i,'p215':ra,'dagPerm':rb}for i,(ra,rb)in enumerate(zip(a['transitions'],b['transitions']))if ra!=rb]
 result={'status':'PYTHON_STRUCTURAL_COMPARISON_NOT_KERNEL_CHECKED',
   'programs':['Prog215.v','DagPerm.v'],
   'expanded_leaf_counts':[dict(Counter(op for _,op,_ in x['leaves']))for x in [a,b]],
   'primitive_counts':[len(x['primitive'])for x in [a,b]],
   'ordered_primitive_effects_equal':effects_a==effects_b,
   'initial_ordinals':[x['initial']for x in [a,b]],
   'ordinal_transitions_equal':a['transitions']==b['transitions'],
   'differing_ordinal_count':len(diffs),
   'first_differences':diffs[:20],
   'symbolically_reachable_counts':[len(x['bfs'])for x in [a,b]],
   'canonical_reachable_cfgs_equal':a['canonical']==b['canonical'],
   'epsilon_cache_queries':[x['epsilon_queries']for x in [a,b]],
   'normalization':'Resolve only pure EBreak/EContinue control edges; preserve each ordered EInc/EDecnz/EHalt occurrence and both decrement outcomes. No commutation, reassociation, arithmetic normalization, offset relation, register valuation restriction, or effect elimination.',
   'trust_boundary':'Python-only structural comparison; a generic source-to-flat-CFG semantic theorem and a kernel-checked equality are still required.'}
 for name,x in [('p215',a),('dagPerm',b)]:
  encoded=json.dumps({'initial':x['initial'],'transitions':x['transitions']},separators=(',',':')).encode()
  (HERE/(name+'_flat_cfg.json')).write_bytes(encoded+b'\n')
  result[name+'_flat_cfg_sha256']=hashlib.sha256(encoded+b'\n').hexdigest()
 (HERE/'flat_cfg_result.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
