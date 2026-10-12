"""Finite rational tests of the all-rank spectral normalization."""
from pathlib import Path
from itertools import combinations,permutations
from fractions import Fraction
import json
import sympy as S
from compiler import direct_determinant
if not __debug__:raise RuntimeError('Do not use -O.')
root=Path(__file__).resolve().parents[1]
def sign(p):return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
count=0
for r in range(1,5):
 ps=list(permutations(range(r)))
 for ss in [2,3,2*r-1]:
  for m in [r,r+1]:
   total=Fraction(0)
   for ns in combinations(range(1,m+1),r):
    ns=ns[::-1]
    for sig in ps:
     for tau in ps:
      term=Fraction(sign(sig)*sign(tau))
      for j,n in enumerate(ns):term*=Fraction(n)**(sig[j]+tau[j]-ss)
      total+=term
   got=direct_determinant(r,m,[(0,ss,1)])
   assert S.Rational(total.numerator,total.denominator)==got,(r,ss,m)
   count+=1
(root/'data'/'spectral_exact_checks.json').write_text(json.dumps({'all_rank_double_permutation_checks':count,'ranks':[1,2,3,4],'arithmetic':'exact rational'},indent=2))
print(count,'exact all-rank spectral checks passed')
