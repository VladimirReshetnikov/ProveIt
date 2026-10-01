"""Exact half-angle intervals and saddle/strict-tangent constants."""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
def sqrt_bounds(x,scale=10**16):
 k=isqrt(x.numerator*scale**2//x.denominator)
 return Q(k,scale),Q(k+1,scale)
bs=[];lo=hi=Q(1)
for j in range(12):
 bs.append((lo,hi));_,u=sqrt_bounds(1+lo*lo);l,_=sqrt_bounds(1+hi*hi)
 lo,hi=lo/(1+u),hi/(1+l)
upper=sum(Q(4,5)*b/(1+Q(4,5)*b)for a,b in bs)+Q(4,5)*Q(2)**(1-len(bs))
lower=Q(1,2)+sum(Q(3,2**(j+1)+3)for j in range(2,6))
assert upper<1 and lower>Q(33,32)
assert Q(143,100)**2>2
assert (1+Q(81,100)*Q(4,5))/(1+Q(4,5))==Q(206,225)
assert Q(22,7)**2<10 and Q(10,7)**2>2
assert 10*(4+3*Q(10,7))/8<11
assert 1+Q(47,30)+Q(19,30)*Q(4,5)+Q(1,15)*Q(4,5)**2>3
out={'all_checks_passed':True,'tangent_intervals':[[str(a),str(b)]for a,b in bs],'mean_at_four_fifths_upper':str(upper),'mean_at_one_lower':str(lower),'strict_tangent_factor':'206/225','auxiliary_S0_bound':11}
(Path(__file__).resolve().parents[1]/'data/saddle_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('Exact saddle, strict tangent and S0 bounds pass')
