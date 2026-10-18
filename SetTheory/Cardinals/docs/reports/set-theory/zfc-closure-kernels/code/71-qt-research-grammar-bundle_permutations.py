#!/usr/bin/env python3
"""Exact Boolean source family: rearrange four conjunction leaves and cancel
only double negations introduced by the conjunction tree.  Each output retains
all unchanged AX rows, protected stack tail, input events and cleanup/gate.
"""
import sys,itertools,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
REF=HERE/'reference/theory_encoding'
sys.path.insert(0,str(REF))
import boolean_bundle_variants as b
import check_dne_variants as v
original,base,rows,prefix,mapping=b.context()
spec=v.load_spec()
C=spec['bundle_C']('a','b','c'); G=spec['bundle_G']('a','b','c')
vr=v.imp(('rel','a','b'),('all','c',('rel','a','b')))
ve=v.imp(('eq','a','b'),('all','c',('eq','a','b')))
leaves=[C,G,vr,ve]
def trees(xs):
 if len(xs)==1:yield xs[0];return
 for i in range(1,len(xs)):
  for l in trees(xs[:i]):
   for r in trees(xs[i:]):yield (l,r)
def realize(t):return leaves[t] if isinstance(t,int) else v.conjunction(realize(t[0]),realize(t[1]))
def boundary(t,p=()):
 if t in leaves or not isinstance(t,tuple):return []
 out=[p] if v.is_neg(t) and v.is_neg(t[1]) else []
 if t[0]=='imp':return out+boundary(t[1],p+(1,))+boundary(t[2],p+(2,))
 return out
variants=[];seen=set()
for pi,perm in enumerate(itertools.permutations(range(4))):
 for ti,tree in enumerate(trees(perm)):
  formula=realize(tree);paths=boundary(formula)
  for mask in range(1<<len(paths)):
   selected=[p for bit,p in enumerate(paths) if mask&(1<<bit)]
   f=v.normalize(formula,set(selected))
   if f in seen:continue
   seen.add(f)
   row=b.record(f'conjunction_p{pi:02d}_t{ti}_m{mask}',f,[],rows,prefix,mapping)
   row.update(mask=2000+len(variants),proof={'rule':'four_conjunct_tree','permutation':perm,'tree':tree,'boundary_double_negations':selected})
   variants.append(row)
# More than string identity is available: each source formula is a conjunction
# of exactly the same four leaf formulas, followed by named classical DNE.
for r in variants:
 p=r['proof'];f=realize(p['tree']);f=v.normalize(f,{tuple(x) for x in p['boundary_double_negations']})
 assert f==r['bundle']
 assert sorted(p['permutation'])==list(range(4))
oldwords={r['fine_AX'] for r in json.loads((REF/'original_layout_dne_variants.json').read_text())['variants']}
oldwords.update(r['fine_AX'] for r in json.loads((REF/'boolean_local_variants.json').read_text())['variants'])
for row in variants:row['present_in_prior_DNE_or_single_Boolean_family']=row['fine_AX'] in oldwords
payload={'scope':'ABSTRACT LOGICALLY EQUIVALENT SOURCE FAMILY; no table claim','new_family':'conjunction permutation, reassociation, and boundary double-negation cancellation','variants':variants}
(HERE/'bundle_variants.json').write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({'variants':len(variants),'new_fine_words':sum(not r['present_in_prior_DNE_or_single_Boolean_family'] for r in variants),'fine_lengths':sorted({r['fine_length'] for r in variants}),'minimum_zlib':min(r['zlib_bytes_heuristic_only'] for r in variants)},indent=2))
