#!/usr/bin/env python3
"""Exact symbolic checks of finite identities used in the manuscript.
Requires SymPy. The Gram example is synthetic: NOT a computation of L-function zeros.
These checks do not verify the analytic theorems, the upstream GRH proof, or priority.
"""
from sympy import (symbols, Rational, I, Matrix, eye, zeros, factorial,
                   binomial, simplify, cancel, expand, conjugate)

s,z,g = symbols('s z g')
a = symbols('a')

def difference(f):
    return expand(f.subs(s,s+2)-f)

for d in range(7):
    P = sum((j+1)*s**j for j in range(d+1))
    f = P
    for _ in range(d+1):
        f = difference(f)
    assert f == 0
    # Represent g_a(s+2h) by recurrence, with g = g_a(s).
    expr = sum((-1)**(d+1-h)*binomial(d+1,h)*P.subs(s,s+2*h)
               *(g+sum(1/(s+a+2*j) for j in range(h)))
               for h in range(d+2))
    assert expand(expr).coeff(g) == 0
    assert cancel(P/(s-z)-P.subs(s,z)/(s-z)).is_polynomial(s)
print('PASS: polynomial pole cancellation and gamma elimination for degrees 0..6')

for k in range(1,13):
    # Laplace transform of U_k(z,t), evaluated algebraically.
    transform = (1/(s-z)-sum(z**h/s**(h+1) for h in range(k)))/z**(k+1)
    assert cancel(transform-(1/(s-z)+1/z)/s**(k+1)) == 0
    main = 1/(s-1)-sum(1/s**(h+1) for h in range(k+1))
    assert cancel(main-1/((s-1)*s**(k+1))) == 0
    for ell in range(k):
        numer = sum(binomial(ell,h)*(-Rational(1,2))**(ell-h)*z**h
                    for h in range(ell+1))
        assert expand(numer-(z-Rational(1,2))**ell) == 0
print('PASS: canonical-factor inversion, pole subtraction and derivative multipliers')

# Synthetic spectra with two characters, both sharing ordinates and having
# multiplicity > 1. Two degrees (0 and 1), four tail ordinates above H=10.
# Every column below is shared by both characters.
ordinates = [11,12,13,14]
mults = [(1,1),(1,2),(2,1),(1,3)]
k = 2
columns = []
for gamma, (m1,m2) in zip(ordinates,mults):
    v = Matrix([m1,m1*I*gamma,m2,m2*I*gamma])
    columns.append(v/(Rational(1,2)+I*gamma)**(k+1))
W = Matrix.hstack(*columns).applyfunc(simplify)
assert simplify(W.det()) != 0
G = (W*W.conjugate().T).applyfunc(simplify)
assert G == G.conjugate().T
for n in range(1,5):
    assert simplify(G[:n,:n].det()) > 0
assert simplify(G.det() - W.det()*conjugate(W.det())) == 0
lower = simplify(G.det()/G.trace()**3)
assert lower > 0
print('PASS: exact positive Gram certificate for a synthetic shared-zero spectrum')
print('Synthetic lower bound (decimal for readability):', lower.evalf(10))
print('No actual zeros or analytic assertions were tested.')
