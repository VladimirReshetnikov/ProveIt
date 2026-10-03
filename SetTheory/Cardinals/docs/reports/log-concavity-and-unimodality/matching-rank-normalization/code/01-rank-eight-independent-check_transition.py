from itertools import combinations,combinations_with_replacement,permutations
from functools import lru_cache
import json,hashlib
from pathlib import Path
import sys
BASE=Path(__file__).resolve().parent.parent
@lru_cache(None)
def images(rows):
 return frozenset(sum(1<<j for j in p) for p in permutations(range(4),len(rows)) if all(mask>>j&1 for mask,j in zip(rows,p)))
out=[]
for H in (1,3,7,15):
 counts={}; sha=hashlib.sha256(); neg=0
 for rows in combinations_with_replacement(range(1,16),5):
  Q=sum(bool(rows[i]&H) and bool(images(rows[:i]+rows[i+1:])) for i in range(5))
  S=0
  for tri in combinations(range(5),3):
   rest=tuple(i for i in range(5) if i not in tri)
   missing=[15^x for x in images(tuple(rows[i] for i in tri))]
   pair_images=images(tuple(rows[i] for i in rest))
   S+=any((a | (1<<b)) in pair_images for a in missing for b in range(4) if H>>b&1 and not a>>b&1)
  if 5*S<9*Q:raise RuntimeError((H,rows,S,Q))
  c=S-2*Q
  if c<0:
   neg+=1
   if (S,Q)!=(9,5):raise RuntimeError('negative profile mismatch')
  counts[c]=counts.get(c,0)+1;sha.update(f'{rows}:{c}\n'.encode())
 out.append(dict(normal_support=H,negative_count=neg,counts=counts,sha256=sha.hexdigest()))
 print(out[-1],flush=True)
original=json.load(open(BASE/'primary'/'check_hyperplane_transition.json'))
for x,y in zip(out,original):
 if x['sha256']!=y['sha256']:raise RuntimeError('independent hash mismatch')
if '--save-certificate' in sys.argv:
 json.dump({'passed':True,'profiles':46512,'results':out},open(BASE.parent/'data'/'transition_result.json','w'),indent=2)
