"""Exact weighted endpoint check of the two-core/two-exterior forced sector."""
from itertools import combinations
from functools import lru_cache
from pathlib import Path
import random,json
@lru_cache(None)
def match(rows):
 if not rows:return True
 r=rows[0]
 while r:
  bit=r&-r;r-=bit
  if match(tuple(x&~bit for x in rows[1:])):return True
 return False

def elementary_support(rows,weights,targets):
 total=0
 for ids in combinations(range(len(rows)),targets.bit_count()):
  if match(tuple(rows[i]&targets for i in ids)):
   p=1
   for i in ids:p*=weights[i]
   total+=p
 return total

def count_right(core,L,u,J,R):
 rows=list(core)+list(L)
 for a in range(3):
  for j,r in enumerate(R):
   if r>>a&1:rows[a]|=1<<(3+j)
 return elementary_support(rows,u,J)

rng=random.Random(32127);checked=0
for rep in range(200):
 core=[rng.randrange(8)for _ in range(3)];L=[rng.randrange(1,8)for _ in range(rng.randrange(3,8))]
 u=[rng.randrange(1,8)for _ in range(3+len(L))];ua=u[0]*u[1]*u[2]
 missing=1<<rng.randrange(3);J=7^missing
 forced=[rng.randrange(1,8),rng.randrange(1,8)]
 feasible=[I for I in range(8)if I.bit_count()==2 and match(tuple(r&I for r in forced))]
 if not feasible:continue
 # Explicit parentheses avoid ambiguity in the endpoint-set mask.
 E=sum(u[a]*u[b]for a,b in combinations(range(3),2)if ((1<<a)|(1<<b))in feasible)
 S=0
 for I in feasible:S|=core[(7^I).bit_length()-1]
 b=elementary_support(L,u[3:],J);c=elementary_support(L,u[3:],7)
 V=0;U=0
 for h,targets in((1,J),(2,7)):
  val=0
  for ids in combinations(range(len(L)),h):
   if match(tuple([S&targets]+[L[i]&targets for i in ids])):
    p=1
    for i in ids:p*=u[i+3]
    val+=p
  if h==1:V=val
  else:U=val
 assert b*U>=c*V,(core,L,u,S,b,c,U,V)
 assert count_right(core,L,u,J|8|16,forced)==E*b+ua*V
 assert count_right(core,L,u,7|8|16,forced)==E*c+ua*U
 for r in range(1,8):
  eligible=match(tuple(forced+[r]))
  assert count_right(core,L,u,J|8|16|32,forced+[r])==(ua*b if eligible else 0)
  assert count_right(core,L,u,7|8|16|32,forced+[r])==(ua*c if eligible else 0)
  checked+=1
out={'status':'passed','weighted_sector_checks':checked,'seed':32127,'scope':'Support partition and Rayleigh inequality checked with exact positive integer activities; the theorem itself uses rank-three Rayleigh.'}
(Path(__file__).resolve().parents[1]/'data'/'two_core_sector_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
