"""Exact finite-field and weighted-count audit of the forced-left matroid model."""
from itertools import combinations
from fractions import Fraction
from math import prod
from random import Random
from pathlib import Path
import json

@__import__('functools').lru_cache(None)
def match(rows):
    if not rows:return True
    row=min(rows,key=int.bit_count)
    if not row:return False
    rest=list(rows);rest.remove(row)
    while row:
        bit=row&-row;row-=bit
        if match(tuple(r&~bit for r in rest)):return True
    return False

def det3(cols,p):
    a,b,c=cols
    return (a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0]))%p

rng=Random(873205);prime=1000000007
cases=0;basis_checks=0;degenerate=0
for s1 in range(8):
 for s2 in range(8):
  for repeat in range(3):
   n=rng.randrange(6);L=[rng.randrange(1,8)for _ in range(n)]
   ul=[rng.randrange(1,8)for _ in L];v=[rng.randrange(1,8)for _ in range(3)]
   a=rng.randrange(6);b=rng.randrange(6);common=[rng.randrange(1,8)for _ in range(rng.randrange(5))]
   c=sum(common);d=sum(x*y for x,y in combinations(common,2));q=a*b+a*c+b*c+d
   if q==0:a=b=1;q=a*b+a*c+b*c+d
   def vec(mask):return [rng.randrange(1,prime)if mask>>j&1 else 0 for j in range(3)]
   r1,r2=vec(s1),vec(s2)
   vectors=[[int(i==j)for j in range(3)]for i in range(3)]+[vec(t)for t in L]+[r1,r2]
   for _ in common:
    alpha,beta=rng.randrange(1,prime),rng.randrange(1,prime)
    vectors.append([(alpha*x+beta*y)%prime for x,y in zip(r1,r2)])
   first_special=3+n
   # Weighted basis specialization in s=1: ordinary outside variables scale with t.
   weights=[Fraction(1,w)for w in v]+list(map(Fraction,ul))+[Fraction(b,q),Fraction(a,q)]+[Fraction(w,q)for w in common]
   model=[Fraction(0)]*4
   for J in combinations(range(len(vectors)),3):
    private=[j for j in J if j<3]
    outside=[j-3 for j in J if 3<=j<first_special]
    special=[j-first_special for j in J if j>=first_special]
    available=7^sum(1<<j for j in private)
    rows=[L[i]&available for i in outside]
    if len(special)==0:expected=match(tuple(rows))
    elif len(special)==1:
     ss=s1 if special[0]==0 else s2 if special[0]==1 else s1|s2
     expected=match(tuple(rows+[ss&available]))
    elif len(special)==2:expected=match(tuple(rows+[s1&available,s2&available]))
    else:expected=False
    actual=det3([vectors[j]for j in J],prime)!=0
    assert actual==expected,(s1,s2,L,J,'finite-field accidental cancellation or identity failure')
    basis_checks+=1
    if actual:model[len(outside)]+=prod(weights[j]for j in J)*q*prod(v)
   # Independently enumerate the sector of the original bipartite graph.
   right=v+[a,b]+common
   rtypes=[1,2]+[3]*len(common)
   core_rows=[s1|sum(1<<(3+j)for j,t in enumerate(rtypes)if t&1),
              s2|sum(1<<(3+j)for j,t in enumerate(rtypes)if t&2)]
   actual=[0]*4
   for k in range(4):
    for I in combinations(range(n),k):
     ww=prod(ul[i]for i in I)
     for JJ in combinations(range(len(right)),k+2):
      mask=sum(1<<j for j in JJ)
      if match(tuple(r&mask for r in core_rows+[L[i]for i in I])):
       actual[k]+=ww*prod(right[j]for j in JJ)
   assert list(model)==actual,(s1,s2,L,model,actual)
   assert actual[1]**2>=3*actual[0]*actual[2]
   assert actual[2]**2>=3*actual[1]*actual[3]
   cases+=1
   if not match((s1,s2)):degenerate+=1
out={'seed':873205,'prime':prime,'weighted_sector_graphs_verified':cases,
 'finite_field_basis_tests':basis_checks,'rank_deficient_core_cases':degenerate,
 'all_exact_polynomial_identities':True,'all_ULC3_checks':True,
 'scope':'Finite exact regression checks; generic determinant identities give the universal proof.'}
(Path(__file__).resolve().parents[1]/'data'/'line_matroid_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
