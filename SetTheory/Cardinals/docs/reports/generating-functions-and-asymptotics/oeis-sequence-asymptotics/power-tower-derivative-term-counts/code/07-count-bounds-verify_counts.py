#!/usr/bin/env python3
"""Independent exact audits of A290268 proved-cell counts; no coefficient conjecture."""
from fractions import Fraction
import sympy as sp

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)

C = tuple(map(Fraction, ('0', '13/72', '5/18', '1/8', '5/9', '29/72', '-1/2', '-23/72', '7/9', '5/8', '1/18', '-7/72')))

def J(d,k):
    return d-1 if k%2 == 0 else (d if d%2 else d-2)

def beta(n):
    if n%2 == 0:
        r=n//2
        return (r+1)*(3*r+2)//2
    r=(n+1)//2
    return (3*r*r+3*r-2)//2

def bulk_prefix(X):
    m=X//2
    even_prefix=1+m*(m+1)*(2*m+5)//2
    return even_prefix if X%2 == 0 else even_prefix+beta(X)

def row_nonzero_prefix(X):
    return sum(max(0,X-2*k-2*d-1-J(d,k))
               for d in range(1,X//2+1) for k in range(X//2+1))

def positive_sum(t):
    return sum(max(0,t-4*r-6*s)
               for r in range(max(0,t//4+1))
               for s in range(max(0,t//6+1)))

def quasipoly(X):
    return Fraction(X**3,36)-Fraction(X**2,24)-Fraction(X,6)+C[X%12]

for X in range(181):
    direct=row_nonzero_prefix(X)
    grouped=positive_sum(X-3)+2*positive_sum(X-6)+positive_sum(X-7)
    require(direct == grouped == quasipoly(X), f"tail count mismatch at {X}")
    require(bulk_prefix(X) == sum(map(beta,range(X+1))), f"bulk count mismatch at {X}")
    # Match the original candidate-cell count minus capped exact-J zero budgets.
    outside=sum(max(0,X-2*k-2*d-1)
                for d in range(1,X//2+1) for k in range(X//2+1))
    zeros=sum(min(J(d,k),max(0,X-2*k-2*d-1))
              for d in range(1,X//2+1) for k in range(X//2+1))
    require(outside-zeros == direct, f"capped row count mismatch at {X}")

z=sp.symbols('z')
G=(z**4+2*z**7+z**8)/((1-z)**2*(1-z**4)*(1-z**6))
P=z*(1+4*z+z*z)/(36*(1-z)**4)-z*(1+z)/(24*(1-z)**3)-z/(6*(1-z)**2)
R=sum(sp.Rational(c.numerator,c.denominator)*z**i for i,c in enumerate(C))/(1-z**12)
require(sp.cancel(G-P-R) == 0, "rational generating-function identity failed")

# Boundary of an exceptional depth-d rectangle: k < 2Q, 0 <= q < Q.
for d in range(3,16):
    Q=(2*d+1)*3**d  # Any positive integer Q obeys this boundary identity.
    require(2*(2*Q-1)+2*d+1+(Q-1) == 5*Q+2*d-2, "rectangle boundary failed")

print('PASS: direct/grouped/exact-J/quasipolynomial counts for 0 <= X <= 180')
print('PASS: exact generating-function identity, hence quasipolynomial for every X >= 0')
print('PASS: exact bulk prefix and exceptional-rectangle order boundary')
