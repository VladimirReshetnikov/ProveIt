"""Exact two-shuffle reconciliation of the old and new S6 candidates."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import json

B=Path(__file__).resolve().parents[1]
def add(out,row,c=Q(1)):
    for k,v in row.items():
        out[k]=out.get(k,Q(0))+c*v
        if not out[k]:del out[k]
    return out
def binomial(n,k):return comb(n,k) if 0<=k<=n else 0
products={
    (2,5):{'GZ5':Q(-15,512),'P7':Q(-5,73728)},
    (3,4):{'B4Z3':Q(-3,32),'P7':Q(-7,368640)}}
def row(p,q):
    out={f'g{a}{7-a}':Q(binomial(a-1,p-1)+binomial(a-1,q-1))
         for a in range(1,7) if binomial(a-1,p-1)+binomial(a-1,q-1)}
    return add(out,products[p,q],Q(-1))
relation=add(row(2,5),row(3,4),Q(-2))
assert relation=={'g25':Q(1),'g43':Q(-5),'g52':Q(-15),'g61':Q(-30),
                 'GZ5':Q(15,512),'B4Z3':Q(-3,16),'P7':Q(11,368640)}
old={'S6':Q(1),'g61':Q(-722,527),'g43':Q(-40,527),'g25':Q(128,155),
     'P7':Q(-15191,28569600),'GZ5':Q(3,124),'B4Z3':Q(2373,10540),'B6L':Q(2)}
new={'S6':Q(1),'g61':Q(12334,527),'g52':Q(384,31),'g43':Q(2136,527),
     'P7':Q(-3179,5713920),'B4Z3':Q(801,2108),'B6L':Q(2)}
difference=add(new.copy(),old,Q(-1))
assert not add(difference,relation,Q(128,155))
result=dict(status='PASS',arithmetic='Exact Python fractions',
    standard_rows=[[2,5],[3,4]],row_coefficients=['1','-2'],
    relation={k:str(v) for k,v in relation.items()},
    residual_difference_multiplier='-128/155',residual_terms=0,
    scope='Exact equality of the two conjectural residuals using proved convergent shuffle rows. Neither S6 residual is proved to vanish.')
(B/'verification/S6-coordinate-change.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
