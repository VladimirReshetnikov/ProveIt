#!/usr/bin/env python3
"""Exact algebra and independent decimal diagnostics for contacts.tex.

Python 3, SymPy and mpmath. Run from any directory:
    python verify_contacts.py --output-dir results
The exact and numerical records are intentionally separate. The numerical
checks are diagnostics, not interval proofs. No source repository is modified.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path
import platform
import time

import sympy as sp
import mpmath as mp

s, p, q, delta, h = sp.symbols('s p q delta h')


def binom_poly(x, k):
    return sp.prod(x-j for j in range(k))/sp.factorial(k)


@lru_cache(None)
def t_polynomials(maximum):
    lam = {j: 2**(2*j)*sp.bernoulli(2*j+1, sp.Rational(1, 4)) /
           (j*(2*j+1)) for j in range(1, maximum+1)}
    ex = [sp.Integer(1)]
    for n in range(1, maximum+1):
        ex.append(sp.expand(s*sum(j*lam[j]*ex[n-j]
                                 for j in range(1, n+1))/n))
    return tuple(sp.expand(sum(
        ex[j]*sp.euler(2*(n-j))*sp.rf(s, 2*(n-j)) /
        (2**(2*(n-j))*sp.factorial(2*(n-j)))
        for j in range(n+1))) for n in range(maximum+1))


@lru_cache(None)
def bk(k, order, shift):
    ts = t_polynomials(k//2)
    return sp.expand(sum(ts[j].subs(s, order) *
                         binom_poly(-order/2-2*j, k-2*j)*shift**(k-2*j)
                         for j in range(k//2+1)))


@lru_cache(None)
def endpoint_coefficient(k, sign=1, translation=sp.Integer(0)):
    # X=N+(a+b)/2+1 and Y=X-translation.
    aa = delta-sp.Rational(1, 2)+translation
    bb = -delta-sp.Rational(1, 2)+translation
    return sp.expand(sum(
        bk(j, p, aa)*bk(k-j, q, bb+1) +
        sign*bk(j, p, aa+1)*bk(k-j, q, bb)
        for j in range(k+1))/4)


def zero(expr):
    return sp.expand(expr) == 0


def convolution(a, b, K):
    return [sp.expand(sum(a[j]*b[k-j] for j in range(k+1)))
            for k in range(K+1)]


def homogeneous(expr, degree):
    poly = sp.Poly(sp.expand(expr), p, q)
    return sp.Add(*(co*p**ij[0]*q**ij[1]
                    for ij, co in poly.terms() if sum(ij) == degree))


def exact_checks():
    start = time.time()
    K = 6
    assertions = []
    def check(name, condition):
        assert condition, name
        assertions.append(name)

    check('centered t1', zero(t_polynomials(2)[1]+s*(2*s+1)/16))
    check('centered t2', zero(t_polynomials(2)[2]-
          s*(20*s**3+108*s**2+211*s+60)/1536))
    cs = [endpoint_coefficient(k, 1) for k in range(K+1)]
    ds = [endpoint_coefficient(k, -1) for k in range(K+1)]
    S, D = p+q, p-q
    ambient_c = [sp.Rational(1, 2), -delta*D/4,
        (4*delta**2*(D**2+2*S)-D**2-2*S**2)/64,
        -delta*D*(4*delta**2*(D**2+6*S+8)-3*D**2-6*S**2-36*S)/384]
    ambient_d = [sp.Integer(0), D/8, -delta*(D**2+2*S)/16,
        D*(12*delta**2*(D**2+6*S+8)-5*D**2-6*S**2-48*S-16)/768]
    for k in range(4):
        check(f'ambient symmetric k={k}', zero(cs[k]-ambient_c[k]))
        check(f'ambient alternating k={k}', zero(ds[k]-ambient_d[k]))

    # Table formulas are independently entered restricted expressions.
    d = 2*delta
    table_c = [sp.Rational(1, 2), -d*D/8,
        ((D**2-8)*d**2-D**2-32)/64,
        -d*D*((D**2-28)*d**2-3*D**2)/768]
    table_d = [sp.Integer(0), D/8, -d*(D**2-8)/32,
        D*(3*d**2*(D**2-28)-5*D**2+56)/768]
    for k in range(4):
        check(f'resonance symmetric m={k}', zero(
            (cs[k]-table_c[k]).subs(q, -2*k-p)))
        check(f'resonance alternating m={k}', zero(
            (ds[k]-table_d[k]).subs(q, -2*k-p)))

    for k in range(K+1):
        for coeff, name, sign in [(cs[k], 'symmetric', 1),
                                  (ds[k], 'alternating', -1)]:
            check(f'{name} spectral degree k={k}',
                  coeff == 0 or sp.Poly(coeff, p, q).total_degree() <= k)
            reflect_sign = (-1)**(k if sign == 1 else k+1)
            check(f'{name} reflection k={k}',
                  zero(coeff.subs(delta, -delta)-reflect_sign*coeff))
            check(f'{name} order exchange k={k}',
                  zero(coeff.xreplace({p:q, q:p})-(-1)**k*coeff))
        # Independent exact specialization from the inherited diagonal
        # Euler-polynomial endpoint law, with no gamma-asymptotic input.
        def aa(j):
            return (-1)**j*sp.euler(j, 0)*sp.rf(s, j)/(2*sp.factorial(j))
        old = sp.Rational(1, 4) if k == 0 else -sum(
            aa(j)*aa(k-j) for j in range(1, k))
        check(f'inherited diagonal k={k}', zero(
            cs[k].subs({p:s, q:s, delta:0})-2*old))
        check(f'diagonal alternating zero k={k}',
              zero(ds[k].subs({p:s, q:s, delta:0})))

    # Translation evaluated directly by shifting all four centered arguments,
    # compared against the ambient generalized-binomial transport.
    for k in range(5):
        for sign, coeffs in [(1, cs), (-1, ds)]:
            transported = sum(coeffs[j]*binom_poly(-(p+q)/2-j, k-j)*h**(k-j)
                              for j in range(k+1))
            check(f'ambient translation sign={sign},k={k}',
                  zero(endpoint_coefficient(k, sign, h)-transported))

    # Top homogeneous coefficients computed separately from exp/cosh/sech.
    sec_p = [sp.euler(k)*p**k/(2**k*sp.factorial(k)) if k % 2 == 0
             else sp.Integer(0) for k in range(K+1)]
    sec_q = [x.xreplace({p:q}) for x in sec_p]
    ex = [(-D*delta/2)**k/sp.factorial(k) for k in range(K+1)]
    pre = convolution(convolution(sec_p, sec_q, K), ex, K)
    for sign, coeffs in [(1, cs), (-1, ds)]:
        parity = 0 if sign == 1 else 1
        hyp = [D**k/(4**k*sp.factorial(k)) if k % 2 == parity
               else sp.Integer(0) for k in range(K+1)]
        predicted = convolution(pre, hyp, K)
        for k in range(K+1):
            check(f'top generator sign={sign},k={k}',
                  zero(homogeneous(coeffs[k], k)-predicted[k]/2))

    # Checks where premature resonance restriction provably loses a jet.
    check('ambient p jet at first contact', zero(sp.diff(cs[1], p)+delta/4))
    check('ambient q jet at first contact', zero(sp.diff(cs[1], q)-delta/4))
    check('tangent jet differs from independent p jet',
          not zero(sp.diff(cs[1].subs(q, -2-p), p)-sp.diff(cs[1], p)))
    first_trans = cs[1]-(p+q)*h/4
    check('translated transverse p jet', zero(
        sp.diff(first_trans, p)+delta/4+h/4))

    a, b = sp.symbols('a b')
    at_res = {q:-2-p, delta:(a-b)/2}
    lower = sp.Rational(1, 2)*(a+b)/2+cs[1].subs(at_res)
    check('first ordinary symmetric normalization', zero(
        lower+(p*a+(-2-p)*b)/4))
    check('first reciprocal alternating coefficient', zero(
        ds[2].subs(at_res)-p*(-2-p)*(a-b)/8))

    # Exact Gamma/digamma endpoint specialization uses recurrence values.
    r = sp.sqrt(2/sp.pi)
    E3 = lambda x: x**3-sp.Rational(3,2)*x**2+sp.Rational(1,4)
    left = r*sp.log(2)*E3(sp.Integer(3))/(2*(2*r)**3)
    right = (1-sp.log(2))/r*E3(sp.Integer(2))*r**3/2
    check('pi log2 first endpoint', sp.simplify(left-55*sp.pi*sp.log(2)/128)==0)
    check('pi log2 second endpoint', sp.simplify(right-
          9*(1-sp.log(2))/(4*sp.pi))==0)

    return {
        'kind':'exact symbolic verification',
        'status':'passed', 'assertion_count':len(assertions),
        'coefficient_orders':f'0 through {K}',
        'independent_diagonal_check':'Euler-polynomial endpoint coefficients',
        'assertions':assertions,
        'ambient_coefficients':{
            str(k):{'symmetric':str(sp.factor(cs[k])),
                    'alternating':str(sp.factor(ds[k]))} for k in range(4)},
        'versions':{'python':platform.python_version(),'sympy':sp.__version__},
        'seconds':round(time.time()-start, 4),
    }


def mprat(x):
    x = sp.Rational(x)
    return mp.mpf(int(x.p))/int(x.q)


def Bfun(order, z):
    if order == 1:
        return (mp.digamma((z+1)/2)-mp.digamma(z/2))/2
    if order == -3:
        return (z**3-mp.mpf('1.5')*z**2+mp.mpf('.25'))/2
    return mp.power(2, -order)*(mp.zeta(order, z/2)-mp.zeta(order, (z+1)/2))


def hfun(z):
    return mp.sqrt(2)*mp.gamma((z+1)/2)/mp.gamma(z/2)


def tau(order, z):
    return mp.exp(order*mp.log(hfun(z)))*Bfun(order, z)


def V(order, z):
    return (mp.power(z, order)-mp.power(z-1, order))*mp.exp(-2*order*mp.log(hfun(z)))


def endpoint(order_p, order_q, a, b, n, sign=1):
    return tau(order_p, n+a+1)*tau(order_q, n+b+2)+sign*\
           tau(order_p, n+a+2)*tau(order_q, n+b+1)


def summand(order_p, order_q, a, b, n, sign=1):
    z, w = n+a+1, n+b+1
    return (V(order_p, z)+sign*V(order_q, w))*tau(order_p, z)*tau(order_q, w)


def specific_coefficients(K, pp, qq, dd):
    pp, qq, dd = map(sp.Rational, (pp,qq,dd))
    # Substitute numerical rational data before expanding; higher-order
    # coefficients therefore remain very small exact rational calculations.
    def bvalue(k, order, shift):
        ts = t_polynomials(k//2)
        return sum(ts[j].subs(s,order)*binom_poly(-order/2-2*j,k-2*j)
                   *shift**(k-2*j) for j in range(k//2+1))
    plus, minus = [], []
    for k in range(K+1):
        left = sum(bvalue(j,pp,dd-sp.Rational(1,2))*
                   bvalue(k-j,qq,-dd+sp.Rational(1,2)) for j in range(k+1))
        right = sum(bvalue(j,pp,dd+sp.Rational(1,2))*
                    bvalue(k-j,qq,-dd-sp.Rational(1,2)) for j in range(k+1))
        plus.append(sp.factor((left+right)/4))
        minus.append(sp.factor((left-right)/4))
    return plus, minus


def numerical_checks():
    start = time.time()
    mp.mp.dps = 85
    rows = []
    def record(name, observed, predicted, tolerance):
        error = abs(observed-predicted)
        assert error < mp.mpf(tolerance), (name, mp.nstr(error,12))
        rows.append({'name':name, 'absolute_error':mp.nstr(error,12),
                     'tolerance':str(tolerance), 'status':'passed'})

    samples = [
        (mp.mpc('1.1','.2'),mp.mpc('.7','-.1'),
         mp.mpc('.8','.1'),mp.mpc('1.3','-.2')),
        (mp.mpf(1),mp.mpf(-3),mp.mpf(1),mp.mpf(2)),
        (mp.mpf(1)/3,-mp.mpf(7)/3,mp.mpf(2)/3,mp.mpf(7)/5),
    ]
    for j, (pp,qq,a,b) in enumerate(samples):
        N=7
        observed_plus=mp.fsum(summand(pp,qq,a,b,n,1) for n in range(N+1))
        predicted_plus=endpoint(pp,qq,a,b,-1,1)-endpoint(pp,qq,a,b,N,1)
        record(f'finite symmetric identity sample {j+1}',observed_plus,predicted_plus,'1e-75')
        observed_minus=mp.fsum((-1)**n*summand(pp,qq,a,b,n,-1) for n in range(N+1))
        predicted_minus=endpoint(pp,qq,a,b,-1,-1)+(-1)**N*endpoint(pp,qq,a,b,N,-1)
        record(f'finite alternating identity sample {j+1}',observed_minus,predicted_minus,'1e-75')

    # Direct finite sums of the two printed ordinary identities, completed
    # by a high-order endpoint remainder. This avoids asking a generic
    # infinite-sum accelerator to resolve a cancellation-prone summand.
    pp,qq,a,b=map(mp.mpf,(1,-3,1,2))
    N=256; X=mp.mpf(N)+mp.mpf('2.5'); K=12
    cp,dp=specific_coefficients(K,sp.Integer(1),sp.Integer(-3),sp.Rational(-1,2))
    observed=mp.fsum(summand(pp,qq,a,b,n,1)+mp.mpf('.5') for n in range(N+1))
    correction=mp.fsum(mprat(cp[k])*X**(1-k) for k in range(2,K+1))
    predicted=55*mp.pi*mp.log(2)/128+9*(1-mp.log(2))/(4*mp.pi)-mp.mpf('1.25')
    record('ordinary symmetric pi log2 identity, 257 terms plus asymptotic remainder',
           observed+correction,predicted,'1e-23')
    observed_minus=mp.fsum((-1)**n*(summand(pp,qq,a,b,n,-1)-1-
        mp.mpf(3)/8*(1/(n+mp.mpf('1.5'))+1/(n+mp.mpf('2.5'))))
        for n in range(N+1))
    correction_minus=-(-1)**N*mp.fsum(mprat(dp[k])*X**(1-k) for k in range(3,K+1))
    predicted_minus=55*mp.pi*mp.log(2)/128-9*(1-mp.log(2))/(4*mp.pi)-mp.mpf('.75')
    record('ordinary alternating pi log2 identity, 257 terms plus asymptotic remainder',
           observed_minus+correction_minus,predicted_minus,'1e-23')

    # Generic noninteger contacts and independent mixed spectral jets:
    # compare exact Gamma--Hurwitz endpoints with the differentiated ambient
    # expansion, without restricting q=-2m-p before differentiation.
    aa=sp.Rational(2,3);bb=sp.Rational(7,5);dd=(aa-bb)/2
    pp=mp.mpf(1)/3; a=mprat(aa);b=mprat(bb);N=1000;X=mp.mpf(N)+(a+b)/2+1
    K=6
    for m in [1,2]:
        qq=-2*m-pp
        for sign in [1,-1]:
            coeffs=[endpoint_coefficient(k,sign).subs(delta,dd) for k in range(K+1)]
            for rj,sj in [(0,0),(1,0),(0,1),(1,1)]:
                total=mp.mpf(0)
                for k,co in enumerate(coeffs):
                    inner=mp.mpf(0)
                    for i in range(rj+1):
                        for j in range(sj+1):
                            dc=sp.diff(co,p,i,q,j)
                            fun=sp.lambdify((p,q),dc,'mpmath')
                            inner+=mp.binomial(rj,i)*mp.binomial(sj,j)*fun(pp,qq)*\
                                   (-mp.log(X)/2)**(rj+sj-i-j)
                    total+=X**(m-k)*inner
                exact=mp.diff(lambda P,Q:endpoint(P,Q,a,b,N,sign),
                              (pp,qq),(rj,sj))
                record(f'ambient endpoint jet m={m},sign={sign},r={rj},s={sj}',
                       exact,total,'1e-10')
    return {'kind':'high-precision numerical diagnostics',
            'status':'passed','precision_decimal_digits':mp.mp.dps,
            'diagnostic_count':len(rows),'diagnostics':rows,
            'evidence_boundary':'Decimal checks, not interval certificates or a substitute for the written proofs.',
            'versions':{'python':platform.python_version(),'mpmath':mp.__version__},
            'seconds':round(time.time()-start,4)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent/'results')
    parser.add_argument('--exact-only',action='store_true')
    parser.add_argument('--numeric-only',action='store_true')
    args=parser.parse_args()
    if args.exact_only and args.numeric_only:
        parser.error('Choose at most one mode selector.')
    args.output_dir.mkdir(parents=True,exist_ok=True)
    if not args.numeric_only:
        report=exact_checks()
        (args.output_dir/'contacts_exact.json').write_text(json.dumps(report,indent=2)+'\n')
        print(f"Exact: {report['assertion_count']} assertions passed.",flush=True)
    if not args.exact_only:
        report=numerical_checks()
        (args.output_dir/'contacts_numeric.json').write_text(json.dumps(report,indent=2)+'\n')
        print(f"Numerical: {report['diagnostic_count']} diagnostics passed at {report['precision_decimal_digits']} digits.",flush=True)

if __name__=='__main__':
    main()
