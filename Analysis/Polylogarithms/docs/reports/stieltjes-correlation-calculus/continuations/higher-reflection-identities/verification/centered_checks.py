"""Finite algebra and numerical diagnostics for the centered classification.

These checks do not replace the difference-algebra and continuation proofs.
All exact checks use rational arithmetic with symbolic zeta constants.
"""
import json
from pathlib import Path

import mpmath as mp
import sympy as s

z,L=s.symbols('z L')
half=s.Rational(1,2)
K=7
f=L-s.Add(*[s.bernoulli(2*k,half)*z**(2*k)/(2*k) for k in range(1,K+1)])
sigf=f.subs({z:z/(1+z),L:L+s.log(1+z)},simultaneous=True)
sigma_res=s.series(sigf-f-z/(1+z/2),z,0,15).removeO().expand()
assert sigma_res==0

def Dx(v):return s.expand(-z*z*s.diff(v,z)+z*s.diff(v,L))

zs={r:s.Symbol('Z'+str(r)) for r in range(2,9)}
gamma=s.Symbol('gamma')
hs={1:f+gamma}
derivative_checks=[]
for r in range(2,9):
    series=zs[r]-z**(r-1)/(r-1)-sum(s.bernoulli(2*k,half)*s.rf(r,2*k-1)*z**(r+2*k-1)/s.factorial(2*k)
               for k in range(1,K+1))
    der=f
    for _ in range(r-1):der=Dx(der)
    target=zs[r]-(-1)**r*der/s.factorial(r-1)
    assert s.series(series-target,z,0,15).removeO().expand()==0
    hs[r]=s.series(series,z,0,15).removeO()
    derivative_checks.append(r)

X=s.symbols('X1:9')
subh={X[r-1]:hs[r] for r in range(1,9)}
inv={X[r-1]:(2*zs[r]-X[r-1] if r%2==0 else X[r-1]) for r in range(1,9)}
examples={
 'odd_orders':X[0]**2*X[2]+X[4],
 'squared_even_tail':(X[1]-zs[2])**2,
 'unequal_even_tails':(X[1]-zs[2])*(X[3]-zs[4]),
 'mixed_invariant':X[0]*(X[1]-zs[2])*(X[5]-zs[6])+X[2]**2,
 'noninvariant_raw_square':X[1]**2,
 'delayed_pole':X[5]-zs[6],
}
records=[]
for name,p in examples.items():
    invariant=s.expand(p.subs(inv,simultaneous=True)-p)==0
    full=s.Poly(s.expand(p.subs(subh)),z)
    odd={str(j):str(s.expand(full.coeff_monomial(z**j))) for j in range(1,14,2)
         if s.expand(full.coeff_monomial(z**j))!=0}
    assert invariant==(not odd)
    records.append({'name':name,'invariant':invariant,'odd_coefficients_through_13':odd})

near_miss=X[1]**3-s.Rational(15,2)*X[1]*X[3]
v=s.expand(near_miss.subs(subh).subs(zs[4],s.Rational(2,5)*zs[2]**2))
assert v.coeff(z,1)==0
assert s.simplify(v.coeff(z,3)-(s.Rational(5,2)*zs[2]-1))==0

def moment_coeff(M):
    rational=-sum(s.binomial(2*M+1,2*M-2*l)*s.bernoulli(2*M-2*l,half)
                 *(2*l-1)*s.bernoulli(2*l-2)/(2*(2*M+1)) for l in range(1,M+1))
    return s.simplify(rational),s.simplify(3*s.bernoulli(2*M,half))

# Independent finite Faulhaber/tail extraction of the rational q blocks.
N,y=s.symbols('N y')
qchecks=[]
for q in range(3,20,2):
    tail=y-y*y/2+sum(s.bernoulli(2*j)*y**(2*j+1) for j in range(1,12))
    power_sum=(s.bernoulli(q-1,N+1)-s.bernoulli(q-1))/(q-1)
    term=s.expand(y**(-q)*tail**2+2*power_sum.subs(N,1/y)*tail)
    actual=term.coeff(y,0)
    expected=-(q-2)*s.bernoulli(q-3)/2
    assert s.simplify(actual-expected)==0
    qchecks.append({'q':q,'constant':str(actual)})

mp.mp.dps=65
numeric=[]
for M in range(4):
    if M==0:
        fun=lambda n:mp.polygamma(1,n+1)**2
    elif M==1:
        fun=lambda n:(n+mp.mpf('.5'))**2*mp.polygamma(1,n+1)**2-1
    elif M==2:
        fun=lambda n:(n+mp.mpf('.5'))**4*mp.polygamma(1,n+1)**2-(n+mp.mpf('.5'))**2+mp.mpf(1)/6
    else:
        fun=lambda n:(n+mp.mpf('.5'))**6*mp.polygamma(1,n+1)**2-(n+mp.mpf('.5'))**4+(n+mp.mpf('.5'))**2/6-mp.mpf(47)/720
    val=mp.nsum(fun,[0,mp.inf])
    a,b=moment_coeff(M)
    target=mp.mpf(str(a.p))/int(a.q)+mp.mpf(str(b.p))/int(b.q)*mp.zeta(3)
    err=abs(val-target)
    assert err<mp.mpf('1e-48')
    numeric.append({'M':M,'value':mp.nstr(val,60),'formula':str(a)+' + ('+str(b)+')*zeta(3)',
                    'absolute_difference':mp.nstr(err,8),'working_dps':mp.mp.dps,
                    'method':'mpmath nsum of an ordinarily convergent bracket; not a rigorous enclosure'})

# Independent explicit head and tail evaluation, with a proved truncation
# envelope. For T(x)=psi'(x+1/2) and
# A_K(x)=sum_{k=0}^K B_{2k}(1/2)/x^(2k+1), the partial fractions
# t/(2 sinh(t/2))=1+2 sum_{k>=1}(-1)^k t^2/(t^2+(2 pi k)^2)
# give |T-A_K| <= C_K/x^(2K+3),
# C_K=2(2K+2)!/(2 pi)^(2K+2). Since 0<T(x)<=1/x and
# |A_K(x)|<=C_A/x for x>=a=N+1/2, summing the squared-tail error
# gives C_K(1+C_A) zeta(2K+4-2M,a).
# This bounds truncation only: mpmath roundoff is not an interval enclosure.
mp.mp.dps=105
tail_N,tail_K=64,30
def mpq(v):return mp.mpf(int(v.p))/int(v.q)
bcoef=[s.bernoulli(2*k,half) for k in range(tail_K+1)]
sqcoef=[sum(bcoef[j]*bcoef[l-j]
            for j in range(max(0,l-tail_K),min(l,tail_K)+1))
        for l in range(2*tail_K+1)]
edge=mp.mpf(tail_N)+mp.mpf('.5')
CA=sum(abs(mpq(bcoef[k]))*edge**(-2*k) for k in range(tail_K+1))
CK=2*mp.factorial(2*tail_K+2)/(2*mp.pi)**(2*tail_K+2)
tail_aware=[]
for M in range(7):
    head=mp.mpf(0)
    for n in range(tail_N):
        x=mp.mpf(n)+mp.mpf('.5')
        polynomial=sum(mpq(sqcoef[l])*x**(2*M-2*l-2) for l in range(M))
        head+=x**(2*M)*mp.polygamma(1,n+1)**2-polynomial
    tail=sum(mpq(sqcoef[l])*mp.zeta(2*l+2-2*M,edge)
             for l in range(M,2*tail_K+1))
    observed=head+tail
    a,b=moment_coeff(M)
    target=mpq(a)+mpq(b)*mp.zeta(3)
    envelope=CK*(1+CA)*mp.zeta(2*tail_K+4-2*M,edge)
    difference=abs(observed-target)
    assert difference<envelope
    tail_aware.append({'M':M,'head_terms':tail_N,'tail_degree':tail_K,
        'working_dps':mp.mp.dps,'value':mp.nstr(observed,80),
        'absolute_difference':mp.nstr(difference,10),
        'analytic_tail_error_envelope':mp.nstr(envelope,10),
        'envelope_scope':'Proved truncation envelope; floating-point evaluations are not rigorous intervals.'})

out={'sigma_recurrence_through_degree':14,'sigma_recurrence_residual':str(sigma_res),
     'derivative_affine_changes_checked':derivative_checks,
     'polynomial_examples':records,'near_miss':{'A1':'0','A3':str(s.Rational(5,2)*zs[2]-1)},
     'faulhaber_constants':qchecks,'moment_values':[
         {'M':M,'rational':str(moment_coeff(M)[0]),'zeta3_coefficient':str(moment_coeff(M)[1])}
         for M in range(11)],'numerical_diagnostics':numeric,
     'remainder_aware_moments':tail_aware}
Path(__file__).with_name('centered_checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'exact_sigma':'PASS','affine_checks':len(derivative_checks),
                  'polynomial_examples':len(records),'faulhaber_blocks':len(qchecks),
                  'numerical':numeric,'remainder_aware':tail_aware},indent=2))
