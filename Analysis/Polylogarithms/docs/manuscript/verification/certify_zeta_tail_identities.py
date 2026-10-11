"""Independent Euler partial fractions and zeta-tail reductions.

The all-order proofs are in Chapter 8. Exact sparse double-zeta coordinates
test the combinatorial reduction, without assuming period independence.
Numerical series checks use a finite Bernoulli tail and a refinement, not
interval certificates. No incoming implementation is imported.
"""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction as Q
from math import factorial
import json
import mpmath as mp
import sympy as s

V=Path(__file__).resolve().parent
x,y,a,p,q,u=s.symbols('x y a p q u')
partial_checks=[];coordinate_checks=[]
def add(out,key,value):
    out[key]+=value
    if not out[key]:del out[key]
def tail_coordinates(r,t,weighted):
    out=defaultdict(Q);f=Q(1,2) if weighted else Q(1)
    shift=2 if weighted else 1
    for key in [('z',r+t-shift),('double',r,t-shift),('double',t,r-shift)]:add(out,key,f)
    return out
for k in range(2,33):
    # Multiply the printed rational identity by its common denominator
    # x^2 y^k (x+y)^(k+1). Check the polynomial directly, avoiding an
    # expensive symbolic rational-denominator search at large orders.
    polynomial=sum(s.binomial(k+i-1,i)*(x+y)**(1-i)*x**i*y**k for i in range(2))
    polynomial+=sum((i+1)*(x+y)**(k-1-i)*x*x*y**i for i in range(k))
    assert s.expand(polynomial-(x+y)**(k+1))==0
    partial_checks.append(k)
    residual=defaultdict(Q)
    for j in range(1,k):
        for key,c in tail_coordinates(j+2,k-j+2,True).items():add(residual,key,(j+1)*(k-j+1)*c)
    for j in range(1,k-1):
        for key,c in tail_coordinates(j+2,k-j+1,False).items():add(residual,key,-Q((j+1)*(k-j),2)*c)
    add(residual,('z',k+2),-Q((k+1)*(k+2),4))
    euler=defaultdict(Q)
    for i in range(2):add(euler,('double',k+i,2-i),Q(s.binomial(k+i-1,i)))
    for i in range(k):add(euler,('double',2+i,k-i),Q(i+1))
    for key in [('double',2,k),('double',k,2),('z',k+2)]:add(euler,key,-1)
    assert dict(residual)==dict(euler)
    coordinate_checks.append(k)
bad=defaultdict(Q,euler);add(bad,('z',34),1)
assert dict(bad)!=dict(euler)

# The first-resonance constants are checked independently as exact Bernoulli
# polynomials, not by importing the report's recurrence or Gamma evaluator.
eta=a/2;d0=a-1-p-q
alpha=[eta,1+p-eta,1+q-eta,d0-u-eta]
c1=-sum(s.bernoulli(3,z) for z in alpha)/3
rho=-d0*p*q
assert s.expand(c1.subs(u,-1)-rho)==0
assert s.expand(s.diff(c1,u).subs(u,-1)/2-s.bernoulli(2,eta)/2+d0*(p+q)/2)==0

mp.mp.dps=70
def product(b,c):
    out=defaultdict(Q)
    for i,ci in b.items():
        for j,cj in c.items():add(out,i+j,ci*cj)
    return dict(out)
def hz_coeff(r,terms):
    coeff={r-1:Q(1,r-1),r:Q(1,2)}
    for j in range(1,terms+1):
        value=Q(s.bernoulli(2*j))*Q(factorial(r+2*j-2),factorial(r-1)*factorial(2*j))
        coeff[r+2*j-1]=value
    return coeff
def tail_polynomial(k,terms):
    out=defaultdict(Q)
    for j in range(1,k):
        pol=product(hz_coeff(j+2,terms),hz_coeff(k-j+2,terms))
        for power,c in pol.items():
            c*=Q((j+1)*(k-j+1));add(out,power-1,c);add(out,power,-c/2)
    for j in range(1,k-1):
        pol=product(hz_coeff(j+2,terms),hz_coeff(k-j+1,terms))
        for power,c in pol.items():add(out,power,-Q((j+1)*(k-j),2)*c)
    return dict(out)
def rational_mp(c):return mp.mpf(c.numerator)/c.denominator
def summand(k,n):
    h=lambda r:mp.zeta(r,n+1)
    return (n+mp.mpf('.5'))*mp.fsum((j+1)*(k-j+1)*h(j+2)*h(k-j+2) for j in range(1,k))-mp.mpf('.5')*mp.fsum((j+1)*(k-j)*h(j+2)*h(k-j+1) for j in range(1,k-1))
def bernoulli_tail(poly,N):return mp.fsum(rational_mp(c)*mp.zeta(power,N+1) for power,c in poly.items())
numeric=[];N=120
for k in range(2,11):
    head=mp.fsum(summand(k,n) for n in range(N))
    coarse=head+bernoulli_tail(tail_polynomial(k,18),N)
    fine=head+bernoulli_tail(tail_polynomial(k,22),N)
    target=mp.mpf((k+1)*(k+2))/4*mp.zeta(k+2)
    error=abs(fine-target);refinement=abs(fine-coarse)
    assert error<mp.mpf('1e-45') and refinement<mp.mpf('1e-45'),(k,error,refinement)
    numeric.append(dict(order=k,absolute_residual=mp.nstr(error,12),tail_refinement=mp.nstr(refinement,12),passed=True))
    print('tail order',k,'PASS',mp.nstr(error,6),flush=True)
# A separate positive centered cubic-tail square uses the explicit expansion
# of (2 zeta(3,k)-k^-3)^2; its target is derived by Tonelli in the manuscript.
coeff={power:2*c for power,c in hz_coeff(3,22).items()}
coeff[3]-=1
pol=product(coeff,coeff)
head=mp.fsum(n*(2*mp.zeta(3,n)-mp.mpf(n)**-3)**2 for n in range(1,N+1))
tail=mp.fsum(rational_mp(c)*mp.zeta(power-1,N+1) for power,c in pol.items())
error=abs(head+tail-(3*mp.zeta(4)-mp.zeta(5)))
assert error<mp.mpf('1e-45'),error
numeric.append(dict(kind='centered-cubic-tail-square',absolute_residual=mp.nstr(error,12),passed=True))
record=dict(status='PASS',partial_fraction_orders=partial_checks,sparse_coordinate_orders=coordinate_checks,
    exact_bernoulli_checks=2,corruption_controls=1,numerical_diagnostics=dict(working_decimal_digits=70,
    head_terms=N,tail_orders=[18,22],interval_certified=False,cases=numeric),
    scope='Independent finite rational identities and sparse Euler/stuffle coordinates; numerical Hurwitz-series sums with Bernoulli-tail refinement. All-order identities rest on the written positive-sum/partial-fraction proof, and numerical residuals are not interval certificates.')
(V/'zeta-tail-identities.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
print('PASS:',len(partial_checks),'partial fractions,',len(coordinate_checks),'coordinate reductions, two Bernoulli checks, one corruption control and',len(numeric),'diagnostics.')
