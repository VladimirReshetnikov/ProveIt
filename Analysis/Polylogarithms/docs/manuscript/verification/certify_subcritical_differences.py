"""Exact fractional-power, difference-sign and Gaussian Euler certificates.

The new proof supplies 57/50 on the triangle and 5/4 on the full axis.
This implementation uses only integer inequalities and rational arithmetic.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from math import comb
import json, sys
sys.set_int_max_str_digits(100000)
B=Path(__file__).resolve().parents[1]
S=10**100
root_checks=0
@lru_cache(None)
def inverse_power(n,exponent):
    global root_checks
    p,q=exponent.numerator,exponent.denominator
    if p==0:return S,S
    target=S**q;factor=n**p
    lo,hi=0,S+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**q*factor<=target:lo=mid
        else:hi=mid
    assert lo**q*factor<=target<(lo+1)**q*factor
    root_checks+=1
    return lo,lo if lo**q*factor==target else lo+1
def coefficients(a,b,last):
    result=[(0,0)];hlo=hhi=0
    for n in range(1,last+1):
        l,u=inverse_power(n,a);result.append((l*hlo,u*hhi))
        bl,bu=inverse_power(n,b);hlo+=bl;hhi+=bu
    return result
def linear(coeffs,terms):
    lower=upper=0
    for n,weight in terms:
        l,u=coeffs[n]
        if weight<0:l,u=u,l
        lower+=weight*l;upper+=weight*u
    return Fraction(lower,S*S),Fraction(upper,S*S)
cases=[];signs=[];N=192
pairs=[(Fraction(1,10),Fraction(1,10)),(Fraction(1,4),Fraction(1,2)),
       (Fraction(1,3),Fraction(1,3)),(Fraction(2,5),Fraction(1,5)),
       (Fraction(1,10),Fraction(9,10)),(Fraction(0),Fraction(1,2)),
       (Fraction(0),Fraction(3,2))]
for a,b in pairs:
    assert a==0 or a+b<=1
    coeffs=coefficients(a,b,2*N-1)
    for n in range(1,9):
        for j in range(11):
            terms=[]
            for k in range(j+1):
                w=(-1)**k*comb(j,k)
                terms.extend([(n+k+1,w),(n+k,-w)])
            lower,upper=linear(coeffs,terms)
            assert lower>0,(a,b,n,j,lower,upper)
            signs.append(dict(a=str(a),b=str(b),n=n,j=j,lower=str(lower),upper=str(upper)))
    weights=[(-1)**k*sum(comb(N,j) for j in range(k+1,N+1)) for k in range(N)]
    el,eu=linear(coeffs,[(2*k+1,w) for k,w in enumerate(weights)])
    el/=2**N;eu/=2**N
    budget=Fraction(57,50) if b<=1 else Fraction(5,4)
    lower=el-budget/2**N;upper=eu
    assert lower<upper<0
    # Every Euler increment after the zero initial term is strictly negative.
    for j in range(1,17):
        dl,du=linear(coeffs,[(2*k+1,(-1)**k*comb(j,k)) for k in range(j+1)])
        assert du<0,(a,b,j)
    cases.append(dict(a=str(a),b=str(b),Euler_terms=N,
        analytic_Gaussian_interval=dict(lower=str(lower),upper=str(upper)),
        width=str(upper-lower),rational_error_constant=str(budget),passed=True))
assert -2*Fraction(cases[-1]['analytic_Gaussian_interval']['upper'])>Fraction(227,200)
record=dict(status='PASS',arithmetic='Standard-library integers and Fractions',
    fractional_grid_digits=100,integer_root_inequalities=root_checks,
    difference_sign_certificates=len(signs),Euler_increment_signs=len(pairs)*16,
    Gaussian_cases=cases,signs=signs,
    scope='Exact finite sign and analytic-value enclosures. The all-parameter error budget, positive difference measure and zero/radial theorems rest on the written proof; ordinary boundary convergence is not asserted below the threshold.')
(B/'verification/subcritical-difference-certificates.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('PASS:',len(signs),'positive Hausdorff-difference signs,',len(pairs)*16,
      'negative Euler increments,',len(cases),'analytic Gaussian enclosures and',root_checks,'integer-root inequalities.')
