"""Independent numerical convention checks for the mixed-generator theorems.

These diagnostics are not premises of the analytic proofs.  The three
resummations use finite Euler evaluations of the defining harmonic sums;
the rational-sampling check uses separately integrated cyclotomic doubles.
"""
from pathlib import Path
import json, time
import mpmath as m
from mixed_gaussian_common import integer_euler_weights

BASE=Path(__file__).resolve().parents[1]
start=time.monotonic()
m.mp.dps=100
L=m.log(2)
P=L**2/4-m.pi**2/48


def direct(t,r=0):
    return -m.quad(lambda y:y**r*m.exp((t-1)*y)*m.log1p(m.exp(-2*y))
                   /(1+m.exp(-2*y)),[0,1,4,16,m.inf])/m.factorial(r)


def B(t):
    return (m.digamma((3-t)/4)-m.digamma((1-t)/4))/4


def continuation(t):
    if m.re(t)<2: return direct(t)
    return (2*B(t-2)-L)/(1-t)-continuation(t-2)


def odd(t): return (continuation(t)-continuation(-t))/2


def harmonic(N,s=1,alternating=False):
    return m.fsum(((-1)**(j-1) if alternating else 1)/m.mpf(j)**s
                  for j in range(1,N+1))


record={'status':'Numerical diagnostics only; analytic proofs are in the article'}
even=[]
for N in range(1,7):
    a=[m.mpf(0)]
    for j in range(1,N+1):a.append(a[-1]+(-1)**(j-1)/m.mpf(2*j-1))
    b=m.fsum(a[j-1]/(2*j-1) for j in range(1,N+1))
    c=m.fsum((-1)**(j-1)/m.mpf(2*j-1)**2 for j in range(1,N+1))
    expected=(-1)**N*(c+2*b-a[-1]*L)
    err=odd(m.mpf(2*N))-expected
    assert abs(err)<m.mpf('1e-90')
    even.append({'t':2*N,'absolute_error':m.nstr(abs(err),8)})
record['even_integer_samples']=even
print('Even integer samples passed',flush=True)

finite_parts=[]
epsilon=m.mpf('1e-25')
for N in range(1,7):
    H=harmonic(N)
    A=harmonic(N,alternating=True)
    e=m.fsum(harmonic(j-1,alternating=True)/j for j in range(1,N+1))
    expected=(-1)**N*(P-L*(H+A)/2
                  +(harmonic(N,2)+harmonic(N,2,True))/4+e/2)
    residue=(-1)**(N+1)*H/2
    err=odd(m.mpf(2*N+1)+epsilon)-residue/epsilon-expected
    assert abs(err)<m.mpf('1e-22')
    finite_parts.append({'pole':2*N+1,'epsilon':str(epsilon),
                         'finite_part_error':m.nstr(err,12)})
record['odd_pole_finite_parts']=finite_parts
print('Odd pole finite parts passed',flush=True)


def cyclotomic_double(a,xi,eta):
    def integrand(x):
        if not x:return m.mpf(0)
        return (-m.log(x))**(a-1)*m.log(1-x/eta)/(x-xi)
    return m.quad(integrand,[0,m.mpf(1)/4,1])/m.factorial(a-1)


samples=[]
for A,d,r in [(1,3,0),(1,3,1),(1,4,0)]:
    alpha=1-m.mpf(2)*A/d
    roots=[m.exp(m.j*m.pi*(2*j+1)/d) for j in range(d)]
    rhs=m.fsum(xi**A*cyclotomic_double(r+1,xi,eta)
               for xi in roots for eta in roots)*(m.mpf(d)/2)**r/2
    err=rhs-direct(alpha,r)
    assert abs(err)<m.mpf('1e-85')
    samples.append({'A':A,'d':d,'derivative_order':r,
                    'absolute_error':m.nstr(abs(err),12)})
record['rational_samples_and_jets']=samples
print('Rational samples and jets passed',flush=True)

# Independently sum the even-index harmonic sums with finite Euler weights.
m.mp.dps=180
L=m.log(2)
M=180
N=650
weights,scale=integer_euler_weights(N)
S=[m.mpf(0)]*M
hn=m.mpf(0)
for n,weight in enumerate(weights):
    if n:hn+=m.mpf(1)/n
    factor=m.mpf(weight)*hn/scale
    r=m.mpf(1)/(2*n+1)**2
    rp=r
    for j in range(M):
        S[j]+=factor*rp
        rp*=r
checks=[]
for t,K,expected in [(1,0,L**2/4-m.pi**2/48),
                      (2,0,L-1),
                      (3,1,L-L**2/4+m.pi**2/48-m.mpf(7)/12)]:
    total=m.fsum(m.mpf(t)**(2*j+1)*(S[j]+(m.mpf(3)**(-2*j-2) if K else 0))
                 for j in range(M))
    d=2*K+3
    tail=harmonic(K+1)*m.mpf(t)**(2*M+1)/d**(2*M+2)/(1-m.mpf(t)**2/d**2)
    error=total-expected
    # The tolerance also allows roundoff in this numerical diagnostic.
    assert abs(error)<=tail+m.mpf('1e-160')
    checks.append({'t':t,'subtracted_poles':K,'terms':M,
                   'error':m.nstr(error,20),
                   'analytic_tail_bound':m.nstr(tail,20)})
record['three_resummations']=checks
record['seconds']=time.monotonic()-start
(BASE/'data/mixed_generator_diagnostics.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
