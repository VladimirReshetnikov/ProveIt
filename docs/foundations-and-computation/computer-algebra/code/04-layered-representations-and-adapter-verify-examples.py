#!/usr/bin/env python3
"""Finite exact checks for the article; not verification of general theorems."""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from pathlib import Path
import platform
import random
import sympy as sp

checks: list[tuple[str, bool]] = []

def check(name: str, condition: object) -> None:
    result = bool(condition)
    checks.append((name, result))
    if not result:
        raise AssertionError(name)

def zero(name: str, expression: sp.Expr) -> None:
    check(name, sp.cancel(sp.expand(expression)) == 0)

t, z, X, a, b, q = sp.symbols('t z X a b q')

def val(expression: sp.Expr) -> sp.Expr:
    expression = sp.cancel(expression)
    if expression == 0:
        return sp.oo
    num, den = sp.fraction(expression)
    return min(k[0] for k, _ in sp.Poly(num,t).terms()) - min(k[0] for k, _ in sp.Poly(den,t).terms())

def initial(poly: sp.Expr, rho: int) -> tuple[sp.Expr, sp.Expr]:
    scaled = sp.Poly(sp.expand(poly.subs(z,t**rho*X)),X)
    lam = min(val(c) for c in scaled.all_coeffs() if c != 0)
    return lam, sp.expand(scaled.as_expr()*t**(-lam)).coeff(t,0)

P = z**3-t**2*z-t**5
for rho, weight, residual in [(1,3,X**3-X),(3,5,-X-1)]:
    w, I = initial(P,rho)
    check(f'cubic weight at {rho}',w==weight)
    zero(f'cubic initial polynomial at {rho}',I-residual)
roots = [t+t**3/2-sp.Rational(3,8)*t**5,
         -t+t**3/2+sp.Rational(3,8)*t**5, -t**3-t**7]
for j,(root,bound) in enumerate(zip(roots,[9,9,13]),1):
    check(f'cubic approximate root residual {j}',val(P.subs(z,root))>=bound)
Q = z*(z-t**3)*(z-t)*(z-1)
for rho, weight, residual in [(0,0,X**3*(X-1)),(1,3,-X**2*(X-1)),(3,7,X*(X-1))]:
    w,I=initial(Q,rho)
    check(f'quartic weight at {rho}',w==weight)
    zero(f'quartic residual at {rho}',I-residual)
    wd,Id=initial(sp.diff(Q,z),rho)
    check(f'quartic derivative weight at {rho}',wd==weight-rho)
    zero(f'quartic derivative residual at {rho}',Id-sp.diff(residual,X))
zero('sharp quadratic collision',z*(z-t)+t**2/4-(z-t/2)**2)
G=sp.Matrix([[0,0,1],[0,1,0],[1,0,a]])
T=sp.Matrix([[3,0,2*a],[0,2*a,3*b],[2*a,3*b,2*a**2]])
zero('cubic residue Gram determinant',G.det()+1)
zero('cubic trace determinant',T.det()-(4*a**3-27*b**2))
zero('cubic discriminant',sp.discriminant(z**3-a*z-b,z)-(4*a**3-27*b**2))
N=6
E=sum(z**k/sp.factorial(k) for k in range(2*N+2))
R=sp.rem(E,z**2-t,z)
B=sum(t**k/sp.factorial(2*k+1) for k in range(N+1))
zero('exponential quotient residue through t^6',sp.expand(R).coeff(z,1)-B)
h=1+2*z-3*z**2+5*z**3+7*z**4
zero('distinct two-root residue',sp.rem(h,z*(z-t),z).coeff(z,1)-(h.subs(z,t)-h.subs(z,0))/t)
zero('double-root jet residue',sp.rem(h,(z-t)**2,z).coeff(z,1)-sp.diff(h,z).subs(z,t))
s=sp.symbols('s')
u=s+s**3/6+sp.Rational(3,40)*s**5+sp.Rational(5,112)*s**7
zero('arcsine branch residual through s^9',sp.series(sp.sin(u)**2-s**2,s,0,10).removeO())
Wx=sp.Matrix([[0,0,0,0],[1,0,0,t**2],[0,t,0,0],[0,0,1,0]])
Wy=sp.Matrix([[0,0,0,0],[0,0,t,0],[1,0,0,t**2],[0,1,0,0]])
check('coupled commutation',Wx*Wy==Wy*Wx)
check('coupled first equation',Wx**2==t*Wy)
check('coupled second equation',Wy**2==t*Wx)
zero('coupled characteristic polynomial x',Wx.charpoly(X).as_expr()-(X**4-t**3*X))
zero('coupled characteristic polynomial y',Wy.charpoly(X).as_expr()-(X**4-t**3*X))
mats=[sp.eye(4),Wx,Wy,Wx*Wy]
GG=sp.Matrix(4,4,lambda i,j:(mats[i]*mats[j])[3,0])
check('coupled residue Gram matrix',GG==sp.Matrix([[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,t**2]]))
zero('coupled residue Gram determinant',GG.det()-1)
xx=t*q+(2+q**2)*t**3/9
yy=t*q**2+(2+q)*t**3/9
for j,expr in enumerate([sp.sin(xx)**2-t*yy,sp.sin(yy)**2-t*xx],1):
    trunc=sp.series(expr,t,0,6).removeO()
    zero(f'coupled sine correction {j}',sp.rem(trunc,q**3-1,q))

# Construct the auxiliary positive rational functional of Theorem 6.1.
def decompositions(generators: list[tuple[int,...]], target: tuple[int,...]) -> list[tuple[int,...]]:
    r=len(target)
    M=1
    while True:
        w=tuple(M**(r-j-1) for j in range(r))
        vals=[sum(wj*ej for wj,ej in zip(w,e)) for e in generators]
        if all(v>0 for v in vals):
            break
        M*=2
    d=sum(wj*tj for wj,tj in zip(w,target))
    if d<0:
        return []
    bounds=[d//v for v in vals]
    return [ns for ns in product(*(range(B+1) for B in bounds))
            if tuple(sum(ns[k]*generators[k][j] for k in range(len(generators))) for j in range(r))==target]
check('grid with negative lower coordinate',decompositions([(1,-3),(0,1)],(2,-4))==[(2,2)])
check('grid with coincident exponent sums',set(decompositions([(0,1),(0,2)],(0,4)))=={(4,0),(2,1),(0,2)})
check('rank-three positive grid',decompositions([(1,-10,0),(0,1,-4),(0,0,1)],(2,-17,-7))==[(2,3,5)])

rng=random.Random(20260921)
for k in range(10):
    mu,nu=rng.randrange(-3,4),rng.randrange(-3,4)
    alpha,beta=mu+rng.randrange(1,5),nu+rng.randrange(1,5)
    ahat=t**mu*(rng.randrange(1,5)+t)
    bhat=t**nu*(rng.randrange(1,5)-t)
    ea=t**alpha*(1+2*t)
    eb=t**beta*(2-t)
    av,bv=ahat+ea,bhat+eb
    check(f'precision sum {k}',val((av+bv)-(ahat+bhat))>=min(alpha,beta))
    bound=min(alpha+val(bhat),beta+val(ahat),alpha+beta)
    check(f'precision product {k}',val(av*bv-ahat*bhat)>=bound)
    check(f'precision inverse {k}',val(1/av-1/ahat)>=alpha-2*mu)

report=(f'Python {platform.python_version()}\nSymPy {sp.__version__}\n'
        f'Checks: {len(checks)}\nPassed: {sum(ok for _,ok in checks)}\nFailures: 0\n\n'
        +'\n'.join(f'PASS  {name}' for name,_ in checks)
        +'\n\nFinite exact checks only. No arbitrary-support recursion, quantifier-elimination implementation,\n'
         'global surreal-function theorem, or formal proof-assistant verification is claimed.\n')
Path(__file__).with_name('python_verification_report.txt').write_text(report)
print(report)
