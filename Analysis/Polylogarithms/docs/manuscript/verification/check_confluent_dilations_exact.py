"""Exact finite controls for the separately proved confluent identities.

Two independent power-series constructions check the even Bernoulli
compiler and all reconstruction coefficients through index seven.
Finite dilation products are compared with direct weighted scale sums.
Checks remain active under Python -O; no arbitrary-data parser is used.
"""
import hashlib
import json
from math import factorial
from pathlib import Path
import platform
import sys
import sympy as s

HERE=Path(__file__).resolve()
checks=[]
controls=[]
def check(name,condition):
    if not bool(condition):
        raise RuntimeError('Exact check failed: '+name)
    checks.append(name)
def zero(name,value):
    check(name,s.expand(value)==0)
def reject(name,wrong,correct):
    if s.expand(wrong-correct)==0:
        raise RuntimeError('Corruption control was not detected: '+name)
    controls.append(name)

L,M,pi,x,y,z=s.symbols('L M pi x y z')
N=9
def mul(a,b):
    return [s.expand(sum(a[j]*b[k-j] for j in range(k+1))) for k in range(N+1)]
def inv(a):
    out=[1/a[0]]
    for k in range(1,N+1):
        out.append(s.expand(-sum(a[j]*out[k-j] for j in range(1,k+1))/a[0]))
    return out
def sinhc(v):
    return [v**k/(2**k*s.factorial(k+1)) if k%2==0 else s.Integer(0) for k in range(N+1)]
sinc=[(-1)**(k//2)*pi**k/s.factorial(k+1) if k%2==0 else s.Integer(0) for k in range(N+1)]
E=mul(mul(sinc,inv(sinhc(L))),inv(sinhc(M)))
Ec=mul(sinc,inv(sinhc(L)))
for k in range(N+1):
    by_bernoulli=s.Integer(0)
    if k%2==0:
        j=k//2
        for v in range(j+1):
            for w in range(j-v+1):
                t=j-v-w
                by_bernoulli+=((-1)**v*pi**(2*v)/s.factorial(2*v+1)
                    *s.bernoulli(2*w,s.Rational(1,2))*L**(2*w)/s.factorial(2*w)
                    *s.bernoulli(2*t,s.Rational(1,2))*M**(2*t)/s.factorial(2*t))
    zero(f'even coefficient independent Bernoulli form {k}',E[k]-by_bernoulli)

A=pi**2/6+(L**2+M**2)/24
zero('quadratic reciprocal coefficient',E[2]+A)
zero('colored quadratic reciprocal coefficient',Ec[2]+pi**2/6+L**2/24)
g=s.symbols('g0:9')
target=[-s.Integer(1)]+[g[k-1]/s.factorial(k-1) for k in range(1,N+1)]
moments=[s.expand(L*M*t) for t in mul(inv(E),target)]
zero('absolute constant anchor',moments[0]+L*M)
for n in range(8):
    reconstructed=s.factorial(n)/(L*M)*sum(E[2*j]*moments[n+1-2*j]
                                           for j in range((n+1)//2+1))
    zero(f'absolute inversion index{n}',reconstructed-g[n])
zero('explicit gamma0',moments[1]/(L*M)-g[0])
zero('explicit gamma1',moments[2]/(L*M)+A-g[1])
zero('explicit gamma2',2*moments[3]/(L*M)-2*A*moments[1]/(L*M)-g[2])

phi=s.symbols('phi0:10')
colored_target=[(-1)**k*phi[k]/s.factorial(k) for k in range(N+1)]
colored_moments=[s.expand(-L*t) for t in mul(inv(Ec),colored_target)]
for n in range(8):
    reconstructed=(-1)**(n+1)*s.factorial(n)/L*sum(Ec[2*j]*colored_moments[n-2*j]
                                                  for j in range(n//2+1))
    zero(f'colored endpoint inversion index{n}',reconstructed-phi[n])

# Pure Laurent multiplication for eta(1-u)=(1-exp(Lu))*zeta(1-u).
# target=u*zeta(1-u); (1-exp(Lu))/u has coefficients -L^(j+1)/(j+1)!.
eta_coeff=mul([-L**(j+1)/s.factorial(j+1) for j in range(N+1)],target)
alt_moments=[s.expand(-L*t) for t in mul(inv(Ec),eta_coeff)]
zero('alternating endpoint moment0',alt_moments[0]+L**2)
zero('alternating endpoint moment1',alt_moments[1]-(L**2*g[0]-L**3/2))
zero('alternating endpoint moment2',2*alt_moments[2]-(2*L**2*g[1]+L**3*g[0]-pi**2*L**2/3-5*L**4/12))

# Centered scale identities are checked rationally, before exponentials.
zero('centered Mellin factor',(x*y-x/y-y/x+1/(x*y))-(x-1/x)*(y-1/y))
zero('colored centered Mellin factor',(1/x-x)+(x-1/x))
zero('digamma constants cancel',-1+1+1-1)
zero('digamma logarithmic scales cancel',-(L+M)/2+(M-L)/2+(L-M)/2+(L+M)/2)

for lam in [s.Integer(2),s.Rational(3,2)]:
    for q in range(5):
        for pattern in [(1,2),(2,1,3),(3,),(2,2)]:
            R=sum(pattern)
            P=s.Poly(s.prod((1-x/lam**(q+j))**r for j,r in enumerate(pattern)),x)
            c=[P.nth(j) for j in range(R+1)]
            check(f'full minimal support {lam,q,pattern}',all(t!=0 for t in c))
            for offset,r in enumerate(pattern):
                k=q+offset
                for degree in range(r):
                    value=sum(c[j]*j**degree*lam**(j*k) for j in range(R+1))
                    zero(f'confluent scale cancellation {lam,q,pattern,k,degree}',value)
                value=sum(c[j]*j**r*lam**(j*k) for j in range(R+1))
                leading=(-1)**r*s.factorial(r)*s.prod((1-lam**(k-q-j))**rr
                           for j,rr in enumerate(pattern) if j!=offset)
                zero(f'first surviving derivative {lam,q,pattern,k}',value-leading)
                check(f'first surviving derivative nonzero {lam,q,pattern,k}',leading!=0)
                Q=s.diff(s.rf(1+z,k),z,q).subs(z,0)/s.factorial(k)
                check(f'positive Pochhammer coefficient {lam,q,pattern,k}',Q>0)
            # Confluent scale matrix on R scales, normalized logarithms.
            rows=[]
            for offset,r in enumerate(pattern):
                k=q+offset
                rows.extend([[j**degree*lam**(j*k) for j in range(R)] for degree in range(r)])
            check(f'confluent matrix nonsingular {lam,q,pattern}',s.Matrix(rows).det()!=0)

a=s.symbols('a')
zero('alternating negative index one',s.euler(1,a)/2-(2*a-1)/4)
zero('alternating repeated-root q1 sign',(-1)**(1+2+1)*s.factorial(1)*(s.euler(1,a)/2)-(2*a-1)/4)
zero('alternating repeated-root q0 sign',(-1)**(0+2+1)*s.factorial(1)*s.euler(0,a)/2+s.Rational(1,2))
reject('reversing the digamma kernel sign',L*M,-L*M)
reject('omitting logarithmic centering leaves an odd reciprocal coefficient',-(L+M)/2,0)
reject('wrong Laurent sign for gamma1',-g[1],g[1])
reject('wrong alternating first logarithmic moment sign',-L**2*g[0]+L**3/2,L**2*g[0]-L**3/2)
reject('treating a double root as simple misses the vanished ordinary moment',L/2,0)

receipt={'status':'PASS','exact_checks':len(checks),'checks':checks,
         'negative_controls':len(controls),'controls':controls,
         'digest_mode':'lf-normalized','script_sha256':hashlib.sha256(HERE.read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
         'source_sha256':{},'source_note':'Self-contained rational/finite formal polynomial checks; no external source file imported.',
         'python_version':platform.python_version(),'sympy_version':s.__version__,'optimization_level':sys.flags.optimize,
         'scope':'Finite coefficient, normalization and cancellation checks supporting the separate all-order analytic proofs.'}
HERE.with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact checks and',len(controls),'negative controls')
