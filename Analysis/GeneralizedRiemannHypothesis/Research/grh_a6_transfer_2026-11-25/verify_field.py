#!/usr/bin/env python3
"""Exact polynomial data. Requires SymPy. No numerical zero computation."""
from sympy import symbols, Poly, discriminant, factor_list, primerange
from collections import Counter
import csv, warnings
from sympy.utilities.exceptions import SymPyDeprecationWarning
warnings.filterwarnings('ignore',category=SymPyDeprecationWarning)
x=symbols('x');f=x**6-2*x**5-x**4+2*x**2-1
assert discriminant(f,x)==2**6*67**2
print('f =',f,'disc =',discriminant(f,x))

def types(p):
    fs=factor_list(f,modulus=p)[1]
    assert all(m==1 for _,m in fs)
    assert all(Poly(g,x,modulus=p).is_irreducible for g,_ in fs)
    return tuple(sorted(Poly(g,x).degree() for g,m in fs)),fs

for p,expected in [(3,(1,5)),(5,(2,4)),(109,(1,1,1,3))]:
    pat,fac=types(p);assert pat==expected
    print(p,pat,fac)
print('These factorization patterns and the square discriminant prove Gal(f)=A6 via Jordan.')
# Cross-check with the independent sextic Galois-group routine.
from sympy.polys.numberfields import galois_group
G,alt=galois_group(f,x)
assert G.order()==360 and alt
print('SymPy galois_group cross-check: order',G.order(),'contained in A6:',alt)
# Small, illustrative census only; not evidence for an asymptotic bound.
counts=Counter(); BOUND=5000
for p in primerange(2,BOUND+1):
    if p in (2,67):continue
    pat,_=types(p);counts[pat]+=1
    assert pat in [(1,1,1,1,1,1),(1,1,1,3),(1,1,2,2),(1,5),(2,4),(3,3)]
with open('sample_patterns.csv','w',newline='') as out:
    w=csv.writer(out);w.writerow(['cycle_type','unramified_primes_le_5000'])
    for pat in sorted(counts):w.writerow(['+'.join(map(str,pat)),counts[pat]])
print('Illustrative census up to',BOUND,dict(counts))
