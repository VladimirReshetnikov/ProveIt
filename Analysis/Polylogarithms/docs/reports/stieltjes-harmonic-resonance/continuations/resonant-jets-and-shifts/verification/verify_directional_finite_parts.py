"""Independent finite-part diagnostics for directional double Hurwitz zeta.

The curved diagonal uses the exact stuffle identity. The two nonsymmetric
directions use finite outer sums and an Euler--Maclaurin Hurwitz-zeta tail.
No polar-germ formula is used to evaluate the double-zeta function itself.
The contour average extracts the constant Laurent coefficient.
"""
from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 60
BASE = Path(__file__).resolve().parent.parent / "results"
CUT = 36
EM_TERMS = 22
NODES = 64
RADIUS = mp.mpf('0.02')
BERNOULLI = [mp.bernoulli(2*k) for k in range(1, EM_TERMS+1)]


def double_hurwitz_em(s, t, a):
    """Continue sum_{n>m>=0}(n+a)^(-s)(m+a)^(-t), for t!=1."""
    q = a+CUT
    finite = mp.fsum((n+a)**(-s)*mp.zeta(t,n+a) for n in range(CUT))
    tail = mp.zeta(s+t-1,q)/(t-1)+mp.zeta(s+t,q)/2
    tail += mp.fsum(BERNOULLI[k-1]/mp.factorial(2*k)
                    *mp.rf(t,2*k-1)*mp.zeta(s+t+2*k-1,q)
                    for k in range(1,EM_TERMS+1))
    return mp.zeta(s,a)*mp.zeta(t,a)-finite-tail


def double_hurwitz_inner_one(s,a):
    """Direct continuation at inner exponent 1, avoiding a 0/0 formula."""
    q=a+CUT
    finite=mp.fsum((n+a)**(-s)*(mp.digamma(n+a)-mp.digamma(a))
                   for n in range(CUT))
    tail=-mp.diff(lambda v:mp.zeta(v,q),s)-mp.zeta(s+1,q)/2
    tail-=mp.fsum(BERNOULLI[k-1]/(2*k)*mp.zeta(s+2*k,q)
                   for k in range(1,EM_TERMS+1))
    tail-=mp.digamma(a)*mp.zeta(s,q)
    return finite+tail


def constant_laurent(function):
    samples=[]
    for j in range(NODES):
        eps=RADIUS*mp.exp(2j*mp.pi*(mp.mpf(j)+mp.mpf('0.5'))/NODES)
        samples.append(function(eps))
    return mp.fsum(samples)/NODES


def C(a):
    return (mp.stieltjes(0,a)**2-mp.zeta(2,a))/2


def fmt(x): return mp.nstr(x,52)


def run():
    cases=[]
    a=mp.mpf('0.7'); lam=mp.mpf(3)/5; mu=-mp.mpf(2)/7
    def diagonal(eps):
        u=eps+lam*eps**2+mu*eps**3
        return (mp.zeta(1+u,a)**2-mp.zeta(2+2*u,a))/2
    observed=constant_laurent(diagonal)
    predicted=C(a)-mp.stieltjes(1,a)-lam*mp.stieltjes(0,a)+(3*lam**2-2*mu)/2
    cases.append({'case':'curved exact diagonal','a':fmt(a),'lambda':'3/5','mu':'-2/7',
                  'observed':fmt(observed),'predicted':fmt(predicted),
                  'absolute_error':fmt(abs(observed-predicted)),
                  'evaluation':'exact diagonal stuffle; independent cubic reparametrization'})
    print('Curved diagonal error:',mp.nstr(abs(observed-predicted),6),flush=True)

    a=mp.mpf('0.7'); c=mp.mpf(2); d=mp.mpf(-1)
    observed=constant_laurent(lambda e:double_hurwitz_em(1+c*e,1+d*e,a))
    predicted=C(a)-d/c*mp.stieltjes(1,a)
    cases.append({'case':'nonsymmetric mixed-sign direction','a':fmt(a),'c':'2','d':'-1',
                  'observed':fmt(observed),'predicted':fmt(predicted),
                  'absolute_error':fmt(abs(observed-predicted)),
                  'evaluation':'finite outer sum and Euler--Maclaurin double-zeta continuation'})
    print('Mixed-sign direction error:',mp.nstr(abs(observed-predicted),6),flush=True)

    a=mp.mpf('1.3'); c=mp.mpf(1)
    observed=constant_laurent(lambda e:double_hurwitz_inner_one(1+c*e,a))
    predicted=C(a)
    cases.append({'case':'inner exponent exactly one','a':fmt(a),'c':'1','d':'0',
                  'observed':fmt(observed),'predicted':fmt(predicted),
                  'absolute_error':fmt(abs(observed-predicted)),
                  'evaluation':'digamma finite outer sum and Euler--Maclaurin tail; no v denominator'})
    print('Inner-one direction error:',mp.nstr(abs(observed-predicted),6),flush=True)
    assert all(mp.mpf(row['absolute_error']) < mp.mpf('1e-45') for row in cases)
    result={'dps':mp.mp.dps,'outer_cutoff':CUT,'Euler_Maclaurin_terms':EM_TERMS,
            'Cauchy_nodes':NODES,'Cauchy_radius':fmt(RADIUS),'cases':cases,
            'status':'Numerical diagnostics with truncated EM tails, not interval certificates.'}
    (BASE/'directional_finite_part_checks.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    run()
