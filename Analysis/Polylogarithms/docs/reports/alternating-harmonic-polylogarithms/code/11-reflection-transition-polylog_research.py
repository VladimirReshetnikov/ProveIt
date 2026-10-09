#!/usr/bin/env python3
"""Reproducible computations for reflection, envelopes, and the depth transition.

Exact certificates use only Python's Fraction/isqrt.  mpmath diagnostics are
independent numerical checks, not interval certificates.  No network access.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import factorial, comb, isqrt
import argparse
import json
from pathlib import Path
import mpmath as mp


def harmonic_elementary(n: int, r: int) -> Q:
    """e_r(1,1/2,...,1/n), with e_0=1."""
    if n < 0 or r < 0:
        raise ValueError('n and r must be nonnegative')
    a = [Q(1)] + [Q(0)] * r
    for k in range(1, n + 1):
        for j in range(min(k, r), 0, -1):
            a[j] += a[j - 1] / k
    return a[r]


def composition_coefficient(r: int, j: int) -> Q:
    """1/r! [x^j](1-x)^(-1)(-log(1-x)/x)^r, exact."""
    a = [Q(1)] * (j + 1)
    for _ in range(r):
        a = [sum((a[k] / (n - k + 1) for k in range(n + 1)), Q(0))
             for n in range(j + 1)]
    return a[j] / factorial(r)


def envelope(p: int, r: int, terms: int) -> tuple[Q, Q]:
    """Exact interval for S_{p,r}; terms starts at n=r, not at n=0."""
    if p < 1 or r < 0 or terms < 0:
        raise ValueError('require integer p>=1, r>=0, terms>=0')
    e = [Q(1)] + [Q(0)] * r
    total = Q(0)
    stop = r + terms
    for n in range(stop + 1):
        if n:
            for j in range(min(n, r), 0, -1):
                e[j] += e[j-1] / n
        term = (-1)**n * e[r] / (2*n+1)**p
        if n < stop:
            total += term
    return min(total, total + term), max(total, total + term)


def iadd(a: tuple[Q,Q], b: tuple[Q,Q]) -> tuple[Q,Q]:
    return a[0]+b[0], a[1]+b[1]


def imul(a: tuple[Q,Q], b: tuple[Q,Q]) -> tuple[Q,Q]:
    v = [x*y for x in a for y in b]
    return min(v), max(v)


def log2_interval(terms: int) -> tuple[Q,Q]:
    lo = 2*sum((Q(1, (2*k+1)*3**(2*k+1)) for k in range(terms)), Q(0))
    return lo, lo + Q(9, 4*(2*terms+1)*3**(2*terms+1))


def inverse_sqrt2_interval(bits: int) -> tuple[Q,Q]:
    m = isqrt(1 << (2*bits-1))
    return Q(m, 1 << bits), Q(m+1, 1 << bits)


def pow2(k: int) -> Q:
    return Q(2**k) if k >= 0 else Q(1, 2**(-k))


def fast_polynomial(p: int, r: int, terms: int) -> list[Q]:
    """Rational c_l so the N-term approximation is
    2^(-p-1/2) sum_l c_l log(2)^l. Cauchy bound in article.
    """
    if p < 1 or r < 0 or terms < 1:
        raise ValueError('require p>=1, r>=0, terms>=1')
    m = p-1
    # P_n(z,u)=(1/2-z-u)_n/n!, truncated in both variables.
    P = [[Q(0) for _ in range(r+1)] for _ in range(m+1)]
    P[0][0] = Q(1)
    c = [Q(0) for _ in range(p)]
    for n in range(terms):
        a = Q(2*n+1, 2)
        for ell in range(p):
            k = m-ell
            c[ell] += sum((P[j][r] / a**(k-j+1)
                           for j in range(k+1)), Q(0)) / (2**n*factorial(ell))
        P = [[(a*P[j][k] - (P[j-1][k] if j else 0)
               - (P[j][k-1] if k else 0))/(n+1)
              for k in range(r+1)] for j in range(m+1)]
    return c


def fast_certificate(p: int, r: int, terms: int = 160) -> tuple[Q,Q]:
    """Exact rational enclosure including coefficient and analytic tail errors."""
    c = fast_polynomial(p, r, terms)
    logiv = log2_interval(terms+32)
    v = (Q(0), Q(0))
    for coeff in reversed(c):
        v = iadd(imul(v, logiv), (coeff, coeff))
    v = imul(v, inverse_sqrt2_interval(4*terms+64))
    v = imul(v, (pow2(-p), pow2(-p)))
    tail = pow2(p+2*r-1-terms) / (Q(terms)+Q(1,4))
    return v[0]-tail, v[1]+tail


def decimal_outward(x: Q, digits: int, up: bool = False) -> str:
    scale = 10**digits
    n = x.numerator * scale
    z = -((-n)//x.denominator) if up else n//x.denominator
    sign = '-' if z < 0 else ''
    z = abs(z)
    return sign + str(z//scale) + '.' + str(z%scale).zfill(digits)


def mpq(x: Q):
    return mp.mpf(x.numerator)/x.denominator


def t_integral(p, r: int, a=mp.mpf('0.5')):
    p, a = mp.mpf(p), mp.mpf(a)
    if p <= 0 or a <= 0 or r < 0:
        raise ValueError('require real p,a>0 and integer r>=0')
    def f(y):
        if y == 0:
            return mp.mpf(0) if p > 1 else (mp.log(2)**r/2 if p == 1 else mp.inf)
        t = mp.exp(-y)
        return y**(p-1)*mp.exp(-a*y)*mp.log1p(t)**r/(1+t)
    return (-1)**r * mp.quad(f, [0, 1, 4, 16, mp.inf])/(mp.factorial(r)*mp.gamma(p))


def s_integral(p, r: int):
    return t_integral(p,r,mp.mpf('0.5')) / mp.power(2,p)


def beta(s):
    return (mp.zeta(s,mp.mpf(1)/4)-mp.zeta(s,mp.mpf(3)/4))/mp.power(4,s) if s != 1 else mp.pi/4


def secant_coefficients(n: int) -> list[Q]:
    # sec(pi*z/2)=sum c_j*pi^(2j)*z^(2j)
    a = [Q(1)]
    for k in range(1,n+1):
        a.append(-sum((Q((-1)**j,2**(2*j)*factorial(2*j))*a[k-j]
                       for j in range(1,k+1)), Q(0)))
    return a


def odd_formula(m: int):
    sec = secant_coefficients(m)
    value = (2*m+1)*beta(2*m+2)
    value -= mp.pi/2*mpq(sec[m])*mp.pi**(2*m)*mp.log(2)
    for j in range(1,m+1):
        value -= mp.pi/2*mpq(sec[m-j])*mp.pi**(2*(m-j))*(1-mp.power(2,-2*j-1))*mp.zeta(2*j+1)
    return value


def gamma_rhs_coefficients(a, degree: int):
    """Ordinary bivariate Taylor coefficients of Gamma(a-z)Gamma(1-a+z+u)/Gamma(1+u)."""
    a = mp.mpf(a)
    logparts = [{} for _ in range(degree+1)]
    for d in range(1,degree+1):
        pa,pb,p1 = [mp.polygamma(d-1,x) for x in [a,1-a,1]]
        for i in range(d+1):
            j=d-i
            val=mp.binomial(d,i)*pb
            if i==d: val += (-1)**d*pa
            if i==0: val -= p1
            logparts[d][(i,j)]=val/mp.factorial(d)
    homogeneous=[{(0,0):mp.mpf(1)}]+[{} for _ in range(degree)]
    for n in range(1,degree+1):
        cur={}
        for d in range(1,n+1):
            for (i,j),v in logparts[d].items():
                for (k,l),w in homogeneous[n-d].items():
                    key=(i+k,j+l)
                    cur[key]=cur.get(key,mp.mpf(0))+d*v*w/n
        homogeneous[n]=cur
    scale=mp.pi/mp.sin(mp.pi*a)
    return {k:v*scale for part in homogeneous for k,v in part.items()}


def normalized_integral(p, r: int, a=mp.mpf('0.5')):
    """Gamma-expectation evaluator, avoiding the exponentially small raw value."""
    p,a=mp.mpf(p),mp.mpf(a)
    if p <= 0 or a <= 0 or r < 1:
        raise ValueError('require real p,a>0 and integer r>=1')
    root=mp.sqrt(p)
    def f(z):
        w=p+root*z
        if w <= 0: return mp.mpf(0)
        y=w/(r+a)
        t=mp.exp(-y)
        h=mp.exp(r*mp.log(mp.log1p(t)/t)-mp.log1p(t))
        density=mp.exp(mp.log(root)+(p-1)*mp.log(w)-w-mp.loggamma(p))
        return h*density
    points=[-root]+[mp.mpf(x) for x in [-12,-4,0,4,12] if x > -root]+[mp.inf]
    return mp.quad(f,points)


def transition_approximation(p, r: int, a=mp.mpf('0.5')):
    p,a=mp.mpf(p),mp.mpf(a)
    L=p/r
    lam=mp.exp(-(L-mp.log(r)))/2
    leading=mp.exp(-lam)
    correction=((lam**2/2-(a+mp.mpf('0.5'))*lam)*L+5*lam**2/6-2*lam)/r
    return leading,leading*(1+correction)


def run(output: Path, full: bool = False):
    output.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=65
    counts={'exact_composition_identities':0,'exact_envelope_intersections':0,
            'odd_formula_numerical_checks':0,'reflection_numerical_checks':0,
            'certified_intervals':0,'transition_diagnostics':0}
    for r in range(7):
        for j in range(9):
            assert harmonic_elementary(r+j,r)==composition_coefficient(r,j)
            counts['exact_composition_identities']+=1
    certs=[]
    cases=[(1,1),(3,1),(5,1),(7,1),(2,2),(3,2),(4,3),(5,4)]
    for p,r in cases:
        N=180 if full else 150
        lo,hi=fast_certificate(p,r,N)
        assert lo<hi
        for terms in [0,1,2,5,12]:
            el,eh=envelope(p,r,terms)
            assert max(el,lo)<=min(eh,hi)
            counts['exact_envelope_intersections']+=1
        v=s_integral(p,r)
        assert mpq(lo)<v<mpq(hi)
        certs.append({'p':p,'r':r,'N':N,
                      'lower':str(lo),'upper':str(hi),
                      'decimal_lower':decimal_outward(lo,45),
                      'decimal_upper':decimal_outward(hi,45,True),
                      'width':mp.nstr(mpq(hi-lo),10),
                      'independent_quadrature':mp.nstr(v,55)})
        counts['certified_intervals']+=1
    (output/'certified_intervals.json').write_text(json.dumps(certs,indent=2)+'\n')
    odds=[]
    for m in range(9):
        v=s_integral(2*m+1,1); f=odd_formula(m)
        err=abs(v-f)
        assert err<mp.mpf('1e-55')
        odds.append({'p':2*m+1,'value':mp.nstr(v,50),'residual':mp.nstr(err,8)})
        counts['odd_formula_numerical_checks']+=1
    (output/'odd_weight_checks.json').write_text(json.dumps(odds,indent=2)+'\n')
    reflections=[]
    for aa in [Q(1,3),Q(1,2),Q(2,3)]:
        a=mpq(aa); rhs=gamma_rhs_coefficients(a,6)
        cache={}
        def T(p,r,flip=False):
            key=(p,r,flip)
            if key not in cache: cache[key]=t_integral(p,r,1-a if flip else a)
            return cache[key]
        for p in range(1,4):
            for r in range(4):
                lhs=T(p,r)+sum((-1)**(p-1+j)*comb(p-1+j,j)*T(p+j,r-j,True) for j in range(r+1))
                err=abs(lhs-rhs[(p-1,r)])
                assert err<mp.mpf('1e-50'),(aa,p,r,err)
                reflections.append({'a':str(aa),'p':p,'r':r,'residual':mp.nstr(err,8)})
                counts['reflection_numerical_checks']+=1
    (output/'reflection_checks.json').write_text(json.dumps(reflections,indent=2)+'\n')
    trans=[]
    for r in [40,160,640,2560]:
        for c in [-1,0,1]:
            p=r*(mp.log(r)+c)
            val=normalized_integral(p,r)
            lead,corr=transition_approximation(p,r)
            trans.append({'a':'1/2','r':r,'c':c,'p':mp.nstr(p,18),
                          'value':mp.nstr(val,25),'leading':mp.nstr(lead,25),
                          'corrected':mp.nstr(corr,25),
                          'leading_error':mp.nstr(abs(val-lead),12),
                          'corrected_error':mp.nstr(abs(val-corr),12),
                          'scaled_remainder':mp.nstr((val-corr)*r*r/(mp.log(r)+c)**2,12)})
            counts['transition_diagnostics']+=1
    (output/'transition_checks.json').write_text(json.dumps(trans,indent=2)+'\n')
    import csv
    with (output/'transition_checks.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=list(trans[0]));wr.writeheader();wr.writerows(trans)
    summary={'status':'PASS','mpmath_dps':mp.mp.dps,'counts':counts,
             'total_recorded_cases':sum(counts.values()),
             'consistency_checks':sum(counts.values())-counts['transition_diagnostics'],
             'scope':'Exact rational certificates and coefficient identities; other checks are non-rigorous numerical diagnostics. The general theorems are proved in article/reflection_envelopes_depth_transition.tex.',
             'python_note':'No Lean or Wolfram execution was performed.'}
    (output/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results')
    parser.add_argument('--full',action='store_true',help='Use 180 terms for exact certificates.')
    args=parser.parse_args()
    run(args.output,args.full)
