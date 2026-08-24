from fractions import Fraction
from sympy import primerange
P=[p for p in primerange(5,10**5)]
print("num primes in [5,1e5):",len(P))
lam=sum(Fraction((p-1)**2,p**3) for p in P)
print("lambda exact float: %.16f"%float(lam))
var=sum(Fraction((p-1)**2,p**3)*(1-Fraction((p-1)**2,p**3)) for p in P)
print("variance sum q(1-q): %.7f"%float(var))
s1=sum(Fraction(1,p) for p in P)
print("sum 1/p          : %.10f"%float(s1))
# dyadic bands
for lo,hi in [(5,100),(100,1000),(1000,10**4),(10**4,10**5)]:
    b=sum(Fraction((p-1)**2,p**3) for p in P if lo<=p<hi)
    print("band [%d,%d): 1000*E = %.2f   count primes %d"%(lo,hi,1000*float(b),sum(1 for p in P if lo<=p<hi)))
# Poisson expectations
import math
l=float(lam); e=[1000*math.exp(-l)*l**k/math.factorial(k) for k in range(6)]
print("poisson 0..5:",["%.1f"%x for x in e],"tail>=6: %.1f"%(1000-sum(e)))
obs=[176,316,256,152,67,24,9]
exp=e+[1000-sum(e)]
chi=sum((o-x)**2/x for o,x in zip(obs,exp))
print("chi2 (>=6 pooled) = %.3f"%chi)
# expected fraction tau>=2 among drops
t2=sum(Fraction((p-1)**2,p**4) for p in P)
t3=sum(Fraction((p-1)**2,p**5) for p in P)
print("E[frac tau>=2] = %.4f ; E[frac tau>=3] = %.5f"%(float(t2/lam),float(t3/lam)))
