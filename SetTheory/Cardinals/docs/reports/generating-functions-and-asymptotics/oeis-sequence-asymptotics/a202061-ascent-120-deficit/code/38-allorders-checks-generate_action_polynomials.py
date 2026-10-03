#!/usr/bin/env python3
"""Generate any fixed finite number of the universal action polynomials.

The expansion is A(n)/(C F) = sum_j P_j(B) L^-j,
B = kappa + 7 log(L)/3.  Formal series are justified in proof.md.
The runtime grows rapidly with the requested order.

Usage: python generate_action_polynomials.py [order]   (default 3)
"""
import sys
import functools
import sympy as S

R = int(sys.argv[1]) if len(sys.argv)>1 else 3
x,w,u,B = S.symbols('x w u B')

def cut(expr):
    return S.Add(*(a*x**j for (j,),a in S.Poly(S.expand(expr),x).terms() if j<=R))

def mul(a,b):
    return cut(a*b)

def power_unit(a,p):
    # a has constant term one.
    b=cut(a-1)
    value=S.Integer(1); term=S.Integer(1)
    for j in range(1,R+1):
        term=mul(term,b)
        value += S.binomial(p,j)*term
    return cut(value)

def log_unit(a):
    b=cut(a-1)
    value=S.Integer(0); term=S.Integer(1)
    for j in range(1,R+1):
        term=mul(term,b)
        value += (-1)**(j+1)*term/S.Integer(j)
    return cut(value)

def substitute(poly,z):
    value=S.Integer(0); term=S.Integer(1)
    for j in range(R+1):
        value += S.expand(poly).coeff(x,j)*term
        term=mul(term,z)
    return cut(value)

Srow=sum(S.rf(S.Rational(3,2),j)*x**j for j in range(R+1))
logS=log_unit(Srow)
# x=1/k here.  Delta = k(T+w)-k(T), solved as a formal fixed point.
Delta=w/2
for _ in range(R+1):
    shifted_x=mul(x,power_unit(1+x*Delta,-1))
    Delta=cut(w/2+log_unit(1+x*Delta)-substitute(logS,shifted_x)+logS)
row_ratio=cut(x*Delta)

@functools.lru_cache(None)
def moment(sign,r,m):
    a=S.Symbol('a',positive=True)
    a0,b0=((S.Rational(3,2),S.Rational(1,2)) if sign == -1
            else (S.Rational(1,2),S.Rational(3,2)))
    b=b0-r
    beta=S.gamma(a)*S.gamma(b0)/S.gamma(a+b0)
    for j in range(r): beta *= (a+b+j)/(b+j)
    value=S.diff(beta,a,m).subs(a,a0)
    return S.simplify(S.expand_func(value)/(S.pi/2))

def integral_series(sign):
    out=S.Integer(1); term=S.Integer(1)
    for r in range(1,R+1):
        term=mul(term,row_ratio)
        for (j,m),coef in S.Poly(term,x,w).terms():
            out += S.binomial(S.Rational(sign,2),r)*coef*moment(sign,r,m)*x**j
    return cut(out)

Jm=integral_series(-1)
Jp=integral_series(+1)
print('Jminus(1/k) =',S.collect(Jm,x),flush=True)
print('Jplus(1/k) =',S.collect(Jp,x),flush=True)

# Now x=1/L.  q=3k/L and B=kappa+7 log(L)/3.
q=S.Integer(1)
for _ in range(R+1):
    r=mul(3*x,power_unit(q,-1))
    q=cut(1+x*(S.Rational(3,2)*B+3*S.log(2)
                +S.Rational(7,2)*log_unit(q)
                -3*substitute(logS,r)-log_unit(substitute(Jm,r))))
r=mul(3*x,power_unit(q,-1))
minus=substitute(Jm,r); plus=substitute(Jp,r)
answer=mul(mul(power_unit(q,S.Rational(2,3)),
               power_unit(minus,-S.Rational(1,3))), (minus+2*plus)/3)
for j in range(R+1):
    val=S.factor(S.simplify(answer.coeff(x,j)))
    print(f'P{j}(B) = {val}',flush=True)
    assert S.Poly(val,B).degree()<=j
    if j:
        assert S.simplify(S.expand(val).coeff(B,j)
             -S.binomial(S.Rational(2,3),j)*S.Rational(3,2)**j)==0
    if j==1: assert S.simplify(val-B)==0
    if j==2: assert S.simplify(val+B*B/4-7*B/2+10)==0
print('PASS: degree bounds, leading coefficients, and available P1/P2 checks',flush=True)
