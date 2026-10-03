#!/usr/bin/env python3
"""Independent exact check of P3/P4 via the original T=log(Y) integrals.

No producer modules are imported or executed.  We derive the row expansion by
residual cancellation, form k^(j)(T)/k(T), integrate the Taylor expansion of
k(T+log z)-k(T), and solve the original duration equation coefficientwise.
Python 3 + SymPy.  Usage: python verify_p3_p4_direct.py
"""
import hashlib
import platform
from pathlib import Path
from functools import lru_cache
import sympy as s

ROOT=Path('/workspace/shared/a202061-allorders-research/action-expansion')
print('Python',platform.python_version(),'SymPy',s.__version__,flush=True)
for filename in ['proof.md','generate_action_polynomials.py']:
    print('SOURCE SHA256',filename,hashlib.sha256((ROOT/filename).read_bytes()).hexdigest(),flush=True)

x, h, A, B, H, g=s.symbols('x h A B H g')
ORDER=4

def coeffs(e, variable=x, order=ORDER):
    """Convert a polynomial to an exact coefficient list."""
    p=s.Poly(s.expand(e),variable)
    return [p.nth(j) for j in range(order+1)]

def add(a,b):
    return [s.expand(u+v) for u,v in zip(a,b)]

def scale(a,c):
    return [s.expand(c*u) for u in a]

def mul(a,b):
    return [s.expand(sum(a[k]*b[j-k] for k in range(j+1))) for j in range(ORDER+1)]

def shift(a,j):
    return [s.S.Zero]*j+a[:ORDER+1-j]

def const(c):
    return [s.sympify(c)]+[s.S.Zero]*ORDER

def inv(a):
    """Reciprocal through triangular coefficient equations."""
    out=[1/a[0]]
    for n in range(1,ORDER+1):
        out.append(s.expand(-sum(a[k]*out[n-k] for k in range(1,n+1))/a[0]))
    return out

def power(a,n):
    out=const(1)
    for _ in range(n): out=mul(out,a)
    return out

def logarithm(a):
    """Integrate a'/a; this does not use a binomial/log power expansion."""
    derivative=[(i+1)*a[i+1] for i in range(ORDER)]+[s.S.Zero]
    quotient=mul(derivative,inv(a))
    return [s.log(a[0])]+[s.expand(quotient[i-1]/i) for i in range(1,ORDER+1)]

def exponential(a):
    """Solve f'=a'f, coefficientwise."""
    out=[s.exp(a[0])]
    for n in range(1,ORDER+1):
        out.append(s.expand(sum(k*a[k]*out[n-k] for k in range(1,n+1))/n))
    return out

def compose_polynomial(expr,arg,variable=A):
    out=const(0)
    for (n,),value in s.Poly(expr,variable).terms():
        out=add(out,scale(power(arg,n),value))
    return out

def as_expr(a,variable=x):
    return sum(c*variable**j for j,c in enumerate(a))

# Derive p1,p2,p3 rather than taking them from the producer.
row=[A]
for j in range(1,4):
    pj=s.Symbol('p'+str(j))
    K=coeffs(s.Rational(1,2)+sum(row[k]*x**(k+1) for k in range(len(row)))+pj*x**(j+1))
    # T^-1=x, x*k=K; log(k/(T/2))=log(2K).
    reciprocal_k=shift(inv(K),1)
    Watson=const(1)
    for m in range(1,5):
        Watson=add(Watson,scale(power(reciprocal_k,m),s.rf(s.Rational(3,2),m)))
    residual=add(scale(logarithm(scale(K,2)),-1),logarithm(Watson))
    row.append(s.expand(-residual[j]))
    print('DERIVED p'+str(j)+'(A) =',row[j],flush=True)
assert row[1]==2*A-3
assert s.expand(row[2]-(-2*A*A+10*A-s.Rational(33,2)))==0
assert s.expand(row[3]-(s.Rational(8,3)*A**3-24*A**2+86*A-120))==0

# Compute convergent beta-log moments from Gamma's local Taylor jet.
# This implementation shifts only the denominator Gamma to a positive argument.
# It then builds exp(log Gamma numerator - log Gamma denominator); no derivative
# of the producer's beta recurrence is used.
@lru_cache(None)
def moment(sign,r,m):
    a0,b0=((s.Rational(3,2),s.Rational(1,2)) if sign==-1 else
           (s.Rational(1,2),s.Rational(3,2)))
    b=b0-r
    d=a0+b
    shift_count=max(0,int(1-d))
    D=d+shift_count
    logjet=const(0)
    for j in range(1,ORDER+1):
        logjet[j]=s.simplify(s.expand_func(s.polygamma(j-1,a0)-s.polygamma(j-1,D))/s.factorial(j))
    gammajet=exponential(logjet)
    prefactor=coeffs(s.rf(d+h,shift_count),h)
    jet=scale(mul(prefactor,gammajet),s.gamma(a0)*s.gamma(b)/s.gamma(D))
    result=s.simplify(jet[m]*s.factorial(m)*2/s.pi)
    return s.expand(result).subs(s.log(2),g)

moment_pairs=[(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,4)]
for sign in [-1,1]:
    for r,m in moment_pairs:
        print('NORMALIZED MOMENT',sign,r,m,'=',moment(sign,r,m),flush=True)

# Encode ALL physical constants through two independent formal quantities:
# H=ell/3+d, B=H+2(ell+c)-2log(3), d=log(Y0), ell=log L.
# Let U=sum u_j*x^j, T=2/(3x)+H+U.  Then xT=tau and
# A=log T+c=(B-H)/2+log 3+log tau.
# H is kept symbolic; cancellation proves the answer depends only on B.
u=s.symbols('u1:5')
tau=coeffs(s.Rational(2,3)+H*x+u[0]*x*x+u[1]*x**3+u[2]*x**4)
Ajet=logarithm(tau)
Ajet[0]=(B-H)/2+g # log3+log(2/3)=log2.
Tinv=inv(tau)
K=add(scale(tau,s.Rational(1,2)),shift(Ajet,1))
for j in range(1,4):
    K=add(K,shift(mul(compose_polynomial(row[j],Ajet),power(Tinv,j)),j+1))
Kinv=inv(K)
# a_j=k^(j)(T)/(j! k(T)).  Orders omitted here first enter x^5.
a1=add(shift(const(s.Rational(1,2)),1),shift(Tinv,2))
a1=add(a1,shift(mul(compose_polynomial(s.diff(row[1],A)-row[1],Ajet),power(Tinv,2)),3))
a1=add(a1,shift(mul(compose_polynomial(s.diff(row[2],A)-2*row[2],Ajet),power(Tinv,3)),4))
a1=mul(a1,Kinv)
a2=scale(shift(power(Tinv,2),3),-s.Rational(1,2))
a2=add(a2,scale(shift(mul(compose_polynomial(s.diff(row[1],A,2)-3*s.diff(row[1],A)+2*row[1],Ajet),power(Tinv,3)),4),s.Rational(1,2)))
a2=mul(a2,Kinv)
a3=scale(mul(shift(power(Tinv,3),4),Kinv),s.Rational(1,3))

def integral(sign):
    out=const(1)
    first=add(add(scale(a1,moment(sign,1,1)),scale(a2,moment(sign,1,2))),scale(a3,moment(sign,1,3)))
    second=add(scale(power(a1,2),moment(sign,2,2)),scale(mul(a1,a2),2*moment(sign,2,3)))
    third=scale(power(a1,3),moment(sign,3,3))
    fourth=scale(power(a1,4),moment(sign,4,4))
    for r,term in enumerate([first,second,third,fourth],1):
        out=add(out,scale(term,s.binomial(s.Rational(sign,2),r)))
    return out

Im,Ip=integral(-1),integral(1)
U=coeffs(sum(u[j-1]*x**j for j in range(1,5)))
# Exact original logarithmic duration residual:
# 0=3U/2-log(3xk)/2+log(2I_-/pi).
duration=add(add(scale(U,s.Rational(3,2)),scale(logarithm(scale(K,3)),-s.Rational(1,2))),logarithm(Im))
solutions={}
for j in range(1,5):
    residual=s.expand(duration[j].subs(solutions))
    solutions[u[j-1]]=s.expand(s.solve(residual,u[j-1])[0])
    print('DERIVED u'+str(j)+' =',solutions[u[j-1]],flush=True)
assert all(s.expand(c.subs(solutions))==0 for c in duration)
print('PASS: original duration residual is zero through x^4',flush=True)
# Exact original normalized action:
# log(A_action/(CF))=U/2+log(3xk)/2+log((Im+2Ip)/3).
logaction=add(add(scale(U,s.Rational(1,2)),scale(logarithm(scale(K,3)),s.Rational(1,2))),logarithm(scale(add(Im,scale(Ip,2)),s.Rational(1,3))))
logaction=[s.expand(c.subs(solutions)) for c in logaction]
result=exponential(logaction)
expected=[s.Integer(1),B,-B*B/4+s.Rational(7,2)*B-10,
          (4*B**3-105*B**2+774*B-2050-27*s.pi**2)/24,
          -(7*B**4-273*B**3+3444*B**2-19768*B-189*s.pi**2*B+1944*s.zeta(3)+999*s.pi**2+46290)/48]
for j,value in enumerate(result):
    value=s.simplify(value)
    print('DIRECT P'+str(j)+'(B) =',s.collect(s.expand(value),B),flush=True)
    difference=s.simplify(value-expected[j])
    print('DIFFERENCE P'+str(j)+' =',difference,flush=True)
    assert difference==0
    assert not value.has(H,g)
    assert s.simplify(s.expand(value).coeff(B,j)-s.binomial(s.Rational(2,3),j)*s.Rational(3,2)**j)==0
print('PASS: global P0-P4 exactly equal the stated action polynomials',flush=True)
print('PASS: all H and log(2) terms cancel; identities are symbolic in arbitrary B',flush=True)
print('SCOPE: independent finite-order algebra check of the classical action; no discrete coefficient/action reduction is claimed',flush=True)
