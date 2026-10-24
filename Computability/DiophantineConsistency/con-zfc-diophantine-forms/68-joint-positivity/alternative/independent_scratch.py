#!/usr/bin/env python3
"""Independent-set elimination of scratch wires in the authored bundle circuit."""
import json
from pathlib import Path
from functools import lru_cache
from build_branch_scratch import deserialize, substitute, psum, mul, serial, free_gate_eliminate
D=Path(__file__).resolve().parent
import sys
output_wires='--output-wires' in sys.argv
horn='--horn' in sys.argv
if output_wires:
 from build_branch_scratch import Branch
 Branch.output_wires=True
obj=free_gate_eliminate(0,horn)
b=next(b for b in obj['branches'] if b['name']=='bundle')
wires=b['wires']; adj=[0]*len(wires)
for i,w in enumerate(wires):
 for t in w['value']:
  for v in t['monomial']:
   if v.startswith('q'):
    j=int(v[1:]);adj[i]|=1<<j;adj[j]|=1<<i
@lru_cache(None)
def mis(mask):
 if not mask:return ()
 i=max((i for i in range(len(wires)) if mask>>i&1),key=lambda i:(adj[i]&mask).bit_count())
 a=mis(mask&~(1<<i));c=(i,)+mis(mask&~((1<<i)|adj[i]))
 return max(a,c,key=len)
chosen=set(mis((1<<len(wires))-1))
print('eliminate',len(chosen),sorted(chosen),flush=True)
rows=[deserialize(r) for r in b['quadratic_residuals']]
# Remove selected defining rows first, then substitute everywhere.
rows=[r for i,r in enumerate(rows) if i not in chosen]
for i in sorted(chosen,reverse=True):rows=[substitute(r,wires[i]['name'],deserialize(wires[i]['value'])) for r in rows]
keep=[w for i,w in enumerate(wires) if i not in chosen]
rename={w['name']:'q'+str(i) for i,w in enumerate(keep)}
def ren(p):
 return {tuple(sorted(rename.get(v,v) for v in m)):c for m,c in p.items()}
rows=[ren(r) for r in rows]
# Remaining wire definitions after substitutions; all references prior.
for w in keep:
 p=deserialize(w['value'])
 for i in sorted(chosen,reverse=True):p=substitute(p,wires[i]['name'],deserialize(wires[i]['value']))
 w['name']=rename[w['name']];w['value']=serial(ren(p))
print('residual terms',sum(map(len,rows)),'degree',max(len(m) for r in rows for m in r),flush=True)
poly=psum(mul(r,r) for r in rows)
b.update(wires=keep,wire_count=len(keep),residual_count=len(rows),quadratic_residuals=[serial(r) for r in rows],sum_of_squares=serial(poly),degree=max(map(len,poly)),monomials=len(poly))
obj['common_wire_count']=max(b['wire_count'] for b in obj['branches']);obj['witness_count']=4+obj['common_wire_count'];obj['degree']=sum(b['degree'] for b in obj['branches']);obj['eliminated_original_bundle_wires']=sorted(chosen);obj['note']='Selected an independent set of constructor dependencies; surviving equations have degree at most4.'
(D/('horn_output_independent.json' if horn else 'branch_scratch_output_independent.json' if output_wires else 'branch_scratch_independent.json')).write_text(json.dumps(obj,indent=2)+'\n')
print('RESULT',obj['witness_count'],obj['degree'],'bundle terms',len(poly),flush=True)
