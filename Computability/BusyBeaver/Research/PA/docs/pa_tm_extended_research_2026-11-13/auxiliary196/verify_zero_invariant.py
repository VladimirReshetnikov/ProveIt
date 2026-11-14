"""Independently check the finite zero/nonzero invariant certificate.

For a mask m, bit r says register r is positive. Positive decrements
nondeterministically produce zero or positive, an exact abstraction of
all positive natural inputs. Therefore closure is a sound induction
certificate for concrete source runs from the given initial frame.
"""
from core import program
from pathlib import Path
import json

ss,ins=program();obj=json.loads(Path('zero_invariants.json').read_text());sets=[]
for s in obj['reachable_masks']:
 x=int(s);assert x>=0 and x.bit_length()<=512
 sets.append({m for m in range(512)if x>>m&1})
assert len(sets)==len(ins)and 1 in sets[25]
edges=0
for pc,ms in enumerate(sets):
 for mask in ms:
  op=ins[pc]
  if op[0]=='inc':
   _,r,q=op;following=[(q,mask|1<<r)]
  elif op[0]=='dec':
   _,r,z,p=op
   following=[(p,mask),(p,mask&~(1<<r))]if mask>>r&1 else[(z,mask)]
  elif op[0]=='jump':following=[(op[1],mask)]
  else:following=[]
  for q,m in following:
   assert m in sets[q],(pc,mask,q,m)
   edges+=1
  z=[r for r in range(9)if all(not(m>>r&1)for m in ms)]
  assert z==obj['known_zero'][pc]
receipt={'status':'PASS','source_points':len(ins),'abstract_states':sum(map(len,sets)),'abstract_edges':edges,'seed_pc':25,'seed_nonzero_mask':1,'meaning':'Concrete seed register0=2, all others zero; finite inductive overapproximation.','closure_checked':True,'kernel_checked':False}
Path('zero_invariant_verification.json').write_text(json.dumps(receipt,indent=2));print(receipt)
