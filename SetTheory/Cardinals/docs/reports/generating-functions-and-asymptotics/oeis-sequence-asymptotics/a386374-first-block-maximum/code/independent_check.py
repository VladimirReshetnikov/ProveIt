#!/usr/bin/env python3
"""Independent finite checks. No floating calculations certify infinite claims."""
import itertools, json, math, sys
from fractions import Fraction as F
from pathlib import Path
import sympy as s

BASE=Path(__file__).resolve().parent
GUARDS=0

def check(ok, message):
    global GUARDS
    GUARDS+=1
    if not ok: raise RuntimeError(message)

def word_counts(n):
    if n==0: return 1,1
    weak=strict=0
    for k in range(1,n+1):
        for w in itertools.product(range(k),repeat=n):
            counts=[w.count(j) for j in range(k)]
            if not all(counts): continue
            other=max(counts[1:],default=0)
            weak += counts[0]>=other
            strict += counts[0]>other
    return weak,strict

# Independent EGF coefficient extraction in exact rational power series.
def egf_counts(N, strict=False):
    coeff=[F(0) for _ in range(N+1)]
    coeff[0]=1
    for first in range(1,N+1):
        max_other=first-int(strict)
        den=[F(0)]+[F(1,math.factorial(j)) for j in range(1,min(max_other,N-first)+1)]
        inv=[F(1)]
        for n in range(1,N-first+1):
            inv.append(sum((den[j]*inv[n-j] for j in range(1,min(n,len(den)-1)+1)), F(0)))
        for n,q in enumerate(inv): coeff[n+first]+=q/math.factorial(first)
    values=[x*math.factorial(n) for n,x in enumerate(coeff)]
    check(all(x.denominator==1 for x in values),'integral EGF coefficients')
    return list(map(int,values))

weak=egf_counts(30)
strict=egf_counts(30,True)
for n in range(8):
    check(word_counts(n)==(weak[n],strict[n]),f'direct words n={n}')
check(all(weak[n+1]>weak[n] for n in range(1,30)),'weak finite strict monotonicity')
check(all(strict[n+1]>strict[n] for n in range(2,30)),'strict finite monotonicity')
# Exact rational checks supporting every numerical inequality in the unit-circle proof.
exp_half=sum(F(1,2**j*math.factorial(j)) for j in range(6))+F(1,2**6*math.factorial(6))/(1-F(1,14))
check(exp_half<F(5,3),'exp(1/2)<5/3')
sin_lower=F(1,8)-F(1,8)**3/6
check(2*F(3,5)*sin_lower>F(1,8),'large-y circle bound')
check(1+F(15,16)+F(15,16)**2/2>F(17,8),'positive real-part circle bound')
check(F(1,120)/(1-F(1,6))==F(1,100),'exponential-tail majorant')
e_upper=sum(F(1,math.factorial(j)) for j in range(6))+F(1,math.factorial(6))/(1-F(1,7))
check(15*(e_upper-2)<11,'weak absolute coefficient error')
check(15*(e_upper-F(5,2))<4,'strict absolute coefficient error')
check(F(10,7)**30>F(14,5)*(10+11*30),'n>=30 inverse denominator bound base')
check(F(31)*30*F(7,10)**30<F(1,2),'n>=30 inverse logarithm bound base')
# Q recurrence checked independently against direct exponential expansion.
v=s.symbols('v')
Bs=s.symbols('B1:5')
Q=[s.Integer(1)]
for ell in range(1,5):
    Q.append(s.expand(sum(j*Bs[j-1]*Q[ell-j] for j in range(1,ell+1))/ell))
expansion=s.exp(sum(Bs[j-1]*v**j for j in range(1,5))).series(v,0,5).removeO().expand()
for ell in range(5): check(s.expand(Q[ell]-expansion.coeff(v,ell))==0,f'Q exponential identity order {ell}')
check(Q[1]==Bs[0],'Q1 formula')
check(s.expand(Q[2]-Bs[1]-Bs[0]**2/2)==0,'Q2 formula')
# Homogeneous monomial degree range and strict h->h+ell rule, through order 4.
x=s.symbols('x')
h=s.symbols('h1:5'); ell=s.symbols('e1:6')
for j in range(1,5):
    poly=s.Poly(Q[j].subs(dict(zip(Bs,[h[k-1]*x**k-ell[k]*x**(k+1) for k in range(1,5)]))),x)
    check(all(j<=monom[0]<=2*j for monom,_ in poly.terms()),f'Q{j} monomial degree range')
shift_expansion=s.exp(sum(ell[k-1]*x**k*v**k for k in range(1,5))).series(v,0,5).removeO().expand()
for j in range(5):
    strict_Q=Q[j].subs(dict(zip(Bs,[Bs[k-1]+ell[k-1]*x**k for k in range(1,5)])), simultaneous=True)
    convolution=sum(Q[k]*shift_expansion.coeff(v,j-k) for k in range(j+1))
    check(s.expand(strict_Q-convolution)==0,f'strict amplitude shift order {j}')
result={'explicit_guard_calls':GUARDS,'strict_amplitude_shift_through_order':4,'direct_words_through_n':7,'rational_egf_through_n':30,'weak_first_22':weak[:22],'strict_first_23':strict[:23],'Q_exponential_identities_through_order':4,'unit_circle_and_inverse_constants':'exact rational checks passed','optimization':sys.flags.optimize,'assert_statements_used':False}
(BASE/('independent_optimized.json' if sys.flags.optimize else 'independent_normal.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
