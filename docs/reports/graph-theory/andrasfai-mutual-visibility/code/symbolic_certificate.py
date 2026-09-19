#!/usr/bin/env python3
"""Exact symbolic checks, not a formalization of the combinatorial proof.

Requires SymPy. Outputs data/symbolic_certificate.txt.
"""
from pathlib import Path
import sympy as s

x, y, z, n = s.symbols('x y z n')
M = s.Matrix([[1,y,0,0], [1,0,y,0], [0,0,0,1], [0,1+y,0,0]])
F = z**4-z**3-y*z**2-y*(1+y)*z+y*(1+y)
D = (1-(3*y**2+6*y+1)*x + y*(3*y**3+11*y**2+12*y+3)*x**2
     -y**2*(y+1)**3*(y+3)*x**3 + y**3*(y+1)**3*x**4)
P = ((y+1)**2*x-y*(3*y**3+7*y**2+6*y+3)*x**2
     +y**2*(3*y**4+10*y**3+11*y**2+6*y+3)*x**3
     -y**3*(y+1)**3*(y**2+3*y+1)*x**4+y**5*(y+1)**3*x**5)
assert s.expand(M.charpoly(z).as_expr()-F) == 0
assert s.expand((s.eye(4)-x*M**3).det()-D) == 0
# Adjugate certificate avoids relying on cancellation in a large inverse.
A = s.eye(4)-x*M**3
assert s.expand(x*s.trace(M**2*A.adjugate()) + y**2*x*D-P) == 0
assert s.gcd(P,D) == 1
assert s.gcd(P.subs(y,1),D.subs(y,1)) == 1
assert s.cancel(P.subs(y,1)/D.subs(y,1)) == s.cancel(
    x*(4-19*x+33*x**2-40*x**3+8*x**4)/(1-10*x+29*x**2-32*x**3+8*x**4))
H = y*z**2/(1-z)+y*(1+y)*z**3
assert s.cancel((1-z)*(1-H)-(s.eye(4)-z*M).det()) == 0

# Finite-deficit polynomials, using polynomial binomials (never interpolation).
def choose_poly(a,k):
    return s.prod(a-i for i in range(k))/s.factorial(k)

lines = ['All exact symbolic assertions passed.', f'SymPy version: {s.__version__}',
         '', 'Characteristic polynomial:', str(F), '', 'Bivariate denominator:',
         str(s.collect(s.expand(D),x)), '', 'Bivariate numerator:',
         str(s.collect(s.expand(P),x)), '', 'Fixed-deficit polynomials:']
from visibility import polynomial
for h in range(5):
    delta = 1+3*h
    expression = 0
    for p in range(1,delta+1):
        for j in range((delta-p)//2+1):
            rest=delta-p-2*j
            if rest % 3:
                continue
            d=rest//3
            assert (1+2*p+j)%3 == 0
            q=n-(1+2*p+j)//3
            expression += ((3*n-1)/s.Integer(p)*choose_poly(p+q-1,p-1)
                           *s.binomial(j+p-1,p-1)*choose_poly(q,d))
    expression=s.factor(expression)
    poly=s.Poly(expression,n)
    assert poly.degree()==3*h+1
    assert poly.LC()==s.Rational(3,s.factorial(3*h+1))
    for value in range(max(2,2*h+1),max(2,2*h+1)+6):
        assert expression.subs(n,value)==polynomial(value)[2*value-1-h]
    lines.append(f'E_{h}(n) = {expression}; valid n >= {max(2,2*h+1)}')

# Implicit differentiation at y=1.
F0=F.subs(y,1)
lambda1=-s.diff(F,y)/s.diff(F,z)
lambda2=-(s.diff(F,z,2)*lambda1**2+2*s.diff(F,z,y)*lambda1+s.diff(F,y,2))/s.diff(F,z)
mu=s.cancel((lambda1/z).subs(y,1))
variance=s.cancel((lambda1/z+lambda2/z-(lambda1/z)**2).subs(y,1))
variance_simple=(46*z**3+18*z**2-40*z+4)/(490*z**3-57*z**2-468*z+166)
assert s.rem(s.together(variance-variance_simple).as_numer_denom()[0],F0,z)==0
assert F0.subs(z,s.Rational(182,100)) < 0
assert F0.subs(z,s.Rational(183,100)) > 0
roots=s.nroots(F0,n=60,maxsteps=200)
lam=max(root for root in roots if abs(s.im(root))<s.Rational(1,10)**50)
eta=max(abs(root) for root in roots if root != lam)
lines += ['', 'Roots at y=1:'] + [str(root) for root in roots]
lines += ['', f'lambda = {lam}', f'alpha = {s.N(lam**3,45)}',
          f'C = {s.N(1/lam,45)}', f'eta = {s.N(eta,45)}',
          f'mu = {s.N(mu.subs(z,lam),45)}',
          f'variance density = {s.N(variance.subs(z,lam),45)}',
          f'variance rational expression = {variance_simple}',
          '', 'All numerical constants above are approximations, not interval certificates.']
path=Path(__file__).resolve().parent.parent/'data'/'symbolic_certificate.txt'
path.write_text('\n'.join(lines)+'\n')
print('\n'.join(lines))
