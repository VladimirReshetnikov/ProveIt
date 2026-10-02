#!/usr/bin/env python3
"""Independent read-only audit. Writes only within this audit directory."""
from pathlib import Path
from fractions import Fraction
import json, math, hashlib, time, sys
import sympy as s
import mpmath as mp

HERE = Path(__file__).resolve().parent
SOURCE = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path('/workspace/shared/oeis-divisor-assembly-research')
u,z,v=s.symbols('u z v'); D=2*u+1
start=time.time()
record=json.loads((SOURCE/'verification.json').read_text())

# Derive phase directly from the logarithm and the exact core saddle identity,
# rather than constructing it from the displayed cumulant formula.
phase=((u-1-s.log(1-v*z))/(1-v*z)+u*(1-v*z)-(2*u-1))/v**2-D*z*z/2
actual=s.series(phase,v,0,11).removeO().expand()
claimed=sum((u+s.harmonic(j)-1)*z**j*v**(j-2) for j in range(3,13))
assert s.expand(actual-claimed)==0
for p in (3,5):
    actual += -s.zeta(-p)**2/s.factorial(p)*v**(2*p)*(1-v*z)**p
A=[s.expand(actual).coeff(v,k) for k in range(11)]

# Independent partition-of-weight summation, not the producer's exponential
# recurrence Q_h=(1/h) sum k A_k Q_(h-k).
def weight_partitions(n,k=1):
    if k>n:
        yield []
        return
    def rec(k,left,items):
        if left==0:
            yield items
            return
        if k>left:return
        for q in range(left//k+1):
            yield from rec(k+1,left-k*q,items+([(k,q)] if q else []))
    yield from rec(k,n,[])

R=[s.Integer(1)]
for m in range(1,6):
    poly=0
    for parts in weight_partitions(2*m):
        term=s.Integer(1)
        for k,q in parts:term*=A[k]**q/s.factorial(q)
        poly+=term
    ans=0
    for (power,),coeff in s.Poly(s.expand(poly),z).terms():
        if power%2==0:
            ans+=coeff*(-1)**(power//2)*s.factorial2(power-1)/D**(power//2)
    R.append(s.factor(ans))
    assert s.factor(R[m]-s.sympify(record['rational_coefficients'][m],locals={'u':u}))==0
assert s.limit((R[3]+s.Rational(1,86400))*u**3,u,s.oo).is_finite

# Mellin residues, including the double-pole coefficient.
a=s.symbols('a')
assert s.residue(s.gamma(a)*s.zeta(a)**2,a,0)==s.Rational(1,4)
residues={p: -s.zeta(-p)**2/s.factorial(p) for p in (1,3,5)}
assert residues=={1:-s.Rational(1,144),3:-s.Rational(1,86400),5:-s.Rational(1,7620480)}

# Independently construct coefficients by multiplying exp(d(k)z^k), through 45.
M=1200
d=[0]*(M+1)
for k in range(1,M+1):
    for j in range(k,M+1,k):d[j]+=1
small=45
b=[Fraction(0) for _ in range(small+1)];b[0]=Fraction(1)
for k in range(1,small+1):
    old=b[:]
    for n in range(small+1):
        b[n]=sum((old[n-k*q]*Fraction(d[k]**q,math.factorial(q)) for q in range(n//k+1)),Fraction(0))
# Bell-polynomial recurrence using binomial coefficients and component counts.
a=[1]
facts=[math.factorial(j) for j in range(M+1)]
for n in range(1,M+1):
    a.append(sum(math.comb(n-1,k-1)*facts[k]*d[k]*a[n-k] for k in range(1,n+1)))
assert all(Fraction(a[n],facts[n])==b[n] for n in range(small+1))
assert a[:11]==[1,1,5,25,193,1481,16021,167665,2220065,30004273,468585541]

mp.mp.dps=75
rf=[s.lambdify(u,r,'mpmath') for r in R]
def params(x):
    N=x-mp.mpf(1)/144
    U=mp.lambertw(2*N*mp.exp(2*mp.euler+2))/2
    return U,mp.sqrt(U/N)
def S(x):
    U,T=params(x);return (2*U-1)/T
def logM(x):
    U,T=params(x)
    return S(x)+mp.mpf(1)/4+mp.mpf(3)/2*mp.log(T)-mp.log(2*mp.pi*(2*U+1))/2
def g(x):return mp.loggamma(x+1)-x*(mp.log(x)-1)+logM(x)
def gp(x):
    U,T=params(x);D=2*U+1
    return mp.digamma(x+1)-mp.log(x)+T-3*T**2/(2*D)-T**2/D**2
rows=[]
for old in record['numerics']:
    n=old['n'];U,T=params(n)
    logbn=mp.log(a[n])-mp.loggamma(n+1)
    ratio=mp.exp(logbn-logM(n))
    partial=mp.mpf(0)
    residuals=[]
    for j in range(6):
        partial+=rf[j](U)*T**j
        r=ratio-partial
        assert abs(r-mp.mpf(old['expansion_residuals'][j]))<mp.mpf('1e-20')
        residuals.append(mp.nstr(r,25))
    y=mp.log(a[n]);X=y/mp.lambertw(y/mp.e);Lam=mp.log(X)
    simple=X-S(X)/Lam+mp.mpf(1)/4
    assert abs(gp(X)-mp.diff(g,X))<mp.mpf('1e-65')
    UX,TX=params(X);DX=2*UX+1
    assert abs(mp.diff(lambda x:params(x)[0],X)-TX**2/DX)<mp.mpf('1e-65')
    assert abs(mp.diff(lambda x:params(x)[1],X)+TX**3/DX)<mp.mpf('1e-65')
    assert abs(mp.diff(S,X)-TX)<mp.mpf('1e-65')
    second=X-g(X)/Lam+g(X)*mp.diff(g,X)/Lam**2-g(X)**2/(2*X*Lam**3)
    assert abs(simple-n-mp.mpf(old['inverse_simple_error']))<mp.mpf('1e-19')
    assert abs(second-n-mp.mpf(old['inverse_second_error']))<mp.mpf('1e-20')
    rows.append({'n':n,'J5_residual':residuals[5],'simple_inverse_error':mp.nstr(simple-n,25),'second_inverse_error':mp.nstr(second-n,25)})

# Symbolic Lagrange coefficients k=1,2,3 from implicit substitution, allowing
# arbitrary g, rather than relying on the reversion formula itself.
X,Lam=s.symbols('X Lam',positive=True)
g0,g1,g2=s.symbols('g0 g1 g2')
lmb=s.symbols('lambda')
c1=-g0/Lam
c2=g0*g1/Lam**2-g0**2/(2*X*Lam**3)
c3=-g0*g1**2/Lam**3-g0**2*g2/(2*Lam**3)+3*g0**2*g1/(2*X*Lam**4)-g0**3/(6*X**2*Lam**4)-g0**3/(2*X**2*Lam**5)
delta=c1*lmb+c2*lmb**2+c3*lmb**3
expr=Lam*delta+delta**2/(2*X)-delta**3/(6*X**2)+lmb*(g0+g1*delta+g2*delta**2/2)
assert all(s.expand(expr).coeff(lmb,k).simplify()==0 for k in (1,2,3))

report={
 'verdict':'No blocking mathematical defect found',
 'direct_phase_generator_check':True,
 'independent_partition_sum_R0_through_R5':True,
 'Mellin_residues':{str(p):str(c) for p,c in residues.items()},
 'independent_exponential_product_sequence_through':small,
 'Bell_recurrence_sequence_through':M,
 'all_reported_numerical_rows_reproduced':True,
 'inverse_implicit_symbolic_check_through_order':3,
 'explicit_parameter_action_g0_derivatives_verified':True,
 'numerics':rows,
 'producer_file_sha256':{name:hashlib.sha256((SOURCE/name).read_bytes()).hexdigest() for name in ('divisor_assembly_asymptotics.tex','verify_divisor_assembly.py','verification.json')},
 'seconds':time.time()-start,
}
(HERE/'audit_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
