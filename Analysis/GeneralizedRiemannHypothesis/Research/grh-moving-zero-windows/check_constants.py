"""Exact rational checks for the rounded constants in report.tex."""
from fractions import Fraction as Q
from math import factorial

# Machin identity and alternating arctan series for bounds on pi.
def atan_bounds(x, n):
    s=sum(((-1)**j*x**(2*j+1)/(2*j+1) for j in range(n)),Q(0))
    t=s+(-1)**n*x**(2*n+1)/(2*n+1)
    return min(s,t),max(s,t)
a,b=atan_bounds(Q(1,5),6); c,d=atan_bounds(Q(1,239),3)
pi_lo,pi_hi=16*a-4*d,16*b-4*c
assert 3<pi_lo<pi_hi<Q(22,7)
assert pi_hi**4/24+pi_hi**2/4<7

# Simple exponential bounds used for the prime and archimedean terms.
assert 1+Q(1,2)+Q(1,8)>Q(8,5)
assert sum((Q(1,factorial(k)) for k in range(5)),Q(0))+Q(1,120)*Q(6,5)<Q(25,9)
assert sum((Q(3**k,factorial(k)) for k in range(5)),Q(0))>12
assert 14*Q(5,3)*(Q(8,3)**2)/pi_lo**2<32
assert (10*Q(15,2)+Q(10,9)*Q(17,2))/(2*pi_lo)<32
assert 32/sum((Q(6**k,factorial(k)) for k in range(10)),Q(0))<pi_lo/32
print("All exact rational constant checks passed.")
