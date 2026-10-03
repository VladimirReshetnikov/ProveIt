"""Independent literal endpoint-set enumeration of small nested graphs."""
from itertools import combinations_with_replacement
from math import comb
from functools import lru_cache
from pathlib import Path
import json
from verify_nested import T

@lru_cache(None)
def perfect(rows):
 if not rows:return True
 first=rows[0]
 return any(perfect(tuple(x&~(1<<b)for x in rows[1:]))for b in range(6)if first>>b&1)

def evaluate(poly,z):return sum(c*z**j for j,c in enumerate(poly))//6

def check(types,n,core):
 # Columns are three right-core vertices followed by individually weighted R.
 weights=[2,3,5]+[7+2*j for j in range(len(types))]
 rows=[((7 if core else 0)|sum(1<<(3+j)for j,t in enumerate(types)if t>>i&1))for i in range(3)]+[7]*n
 literal=[0]*7;formula=[0]*7
 for right in range(1<<len(weights)):
  k=right.bit_count();w=1
  for j,a in enumerate(weights):
   if right>>j&1:w*=a
  for left in range(1<<len(rows)):
   if left.bit_count()!=k:continue
   if perfect(tuple(rows[i]&right for i in range(len(rows))if left>>i&1)):literal[k]+=w
  j=(right&7).bit_count();counts=tuple(sum(1 for z,t in enumerate(types)if t==mask and right>>(3+z)&1)for mask in (1,3,7))
  formula[k]+=w*evaluate(T(j,counts,not core),n-3)
 assert literal==formula,(types,n,core,literal,formula)
 return len(rows),len(weights)

checks=0
for q in range(4):
 for types in combinations_with_replacement((1,3,7),q):
  for n in (3,4):
   for core in (False,True):check(types,n,core);checks+=1
out={'small_graphs_checked':checks,'activities':[2,3,5,7,9,11],'both_core_present_and_deleted':True,'n_values':[3,4],'all_checks_passed':True}
(Path(__file__).resolve().parents[1]/'data'/'small_support_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
