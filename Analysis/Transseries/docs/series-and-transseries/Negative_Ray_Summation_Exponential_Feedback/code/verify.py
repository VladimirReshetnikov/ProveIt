#!/usr/bin/env python3
"""Exact and numerical checks for Negative-Ray Summation of Feedback Transseries.

Python 3.10+. Exact calculations use fractions only. mpmath is used for
non-certified numerical cross-checks, explicitly separated from certificates.
Run from any directory: python code/verify.py --order 24
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from fractions import Fraction as F
from pathlib import Path
from collections import defaultdict
from decimal import Decimal, localcontext

ROOT = Path(__file__).resolve().parents[1]

def mul(a: list[F], b: list[F], n: int) -> list[F]:
    c = [F(0)] * (n + 1)
    for i, x in enumerate(a[:n+1]):
        if x:
            for j, y in enumerate(b[:n+1-i]):
                if y: c[i+j] += x*y
    return c

def compose(a: list[F], b: list[F], n: int) -> list[F]:
    assert b[0] == 0
    out = [F(0)]*(n+1)
    power = [F(1)]+[F(0)]*n
    for ak in a[:n+1]:
        for j in range(n+1): out[j] += ak*power[j]
        power = mul(power, b, n)
    return out

def forward_coefficients(n: int, slope) -> list[F]:
    """U(q)=sum q^j exp(slope(j)*U), by the exponential differential recurrence."""
    u = [F(0)]*(n+1)
    E = [[F(1)] + [F(0)]*n for _ in range(n+1)]
    for m in range(1, n+1):
        u[m] = sum((E[j][m-j] for j in range(1, m+1)), F(0))
        for j in range(1, n-m+1):
            E[j][m] = F(slope(j), m) * sum(
                (i*u[i]*E[j][m-i] for i in range(1, m+1)), F(0))
    return u

def blocks(n: int) -> tuple[list[dict[int,F]], list[int]]:
    """P=e^u Q=sum u^k p_k(e^u), lambda_j=j^2.
    dp[s,l] counts ordered compositions of s into l parts, classified by
    the frequency sum m_i(m_i+1). No floating-point arithmetic is used.
    """
    dp: dict[tuple[int,int], dict[int,int]] = {(0,0): {0:1}}
    polys: list[dict[int,F]] = [{} for _ in range(n+1)]
    polys[1] = {0:F(1)}
    masses = [0]*(n+1); masses[1] = 1
    for s in range(1, n):
        for ell in range(1, s+1):
            d = defaultdict(int)
            for m in range(1, s+1):
                old = dp.get((s-m, ell-1), {})
                shift = m*(m+1)
                for a, count in old.items(): d[a+shift] += count
            if d: dp[s,ell] = dict(d)
        k = s+1
        d2 = defaultdict(F)
        for ell in range(1,k):
            weight = F((-1)**ell * math.comb(k+ell-1,ell), k)
            for a,count in dp[s,ell].items(): d2[a] += weight*count
        polys[k] = {a:w for a,w in sorted(d2.items()) if w}
        mass = sum((F(math.comb(k+ell-1,ell)*math.comb(k-2,ell-1),k)
                    for ell in range(1,k)), F(0))
        assert mass.denominator == 1
        masses[k] = int(mass)
        assert max(polys[k]) <= k*(k-1)
        assert sum(abs(w) for w in polys[k].values()) <= mass
    return polys,masses

def inverse_coefficients(polys, n: int):
    p = [F(0)]*(n+1)
    for degree in range(1,n+1):
        for k in range(1, degree+1):
            m = degree-k
            p[degree] += sum((w*F(a**m,math.factorial(m))
                             for a,w in polys[k].items()), F(0))
    eminus = [F((-1)**m,math.factorial(m)) for m in range(n+1)]
    return p, mul(p,eminus,n)

def schroeder_check(c):
    # S=t(1-S)/(1-2S), so 2 S^2 -(1+t)S+t=0.
    n = len(c)-1
    cc = [F(x) for x in c]
    square = mul(cc,cc,n)
    assert c[1] == 1
    for k in range(2,n+1): assert 2*square[k]-c[k]-c[k-1] == 0

def exp_minus_interval(r: F, terms: int = 36) -> tuple[F,F]:
    """Taylor's integral remainder gives an exact alternating enclosure."""
    assert r >= 0
    total = F(1); term = F(1)
    vals = {}
    for n in range(1, terms+2):
        term *= -r/n; total += term
        if n in (terms,terms+1): vals[n] = total
    return min(vals.values()),max(vals.values())

def add_interval(x,y): return x[0]+y[0], x[1]+y[1]
def scale_interval(c: F, x):
    return (c*x[0],c*x[1]) if c >= 0 else (c*x[1],c*x[0])
def round_interval(x, digits=24):
    d = 10**digits
    low = (x[0].numerator*d)//x[0].denominator
    high = -((-x[1].numerator*d)//x[1].denominator)
    return F(low,d),F(high,d)

def decimal_string(q: F, digits=32) -> str:
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(q.numerator)/Decimal(q.denominator))

def certified_Q(r: F, polys, kmax=14, exp_terms=36):
    """Exact rational enclosure for Q(-r), including the infinite block tail.
    C_k <= 6^k/4 follows from S(1/6)=1/4.
    """
    assert 0 < r < F(1,6)
    tl,th = exp_minus_interval(r, exp_terms)
    assert tl > 0
    maxa = kmax*(kmax-1)
    lp=[F(1)];hp=[F(1)]
    for _ in range(maxa): lp.append(lp[-1]*tl); hp.append(hp[-1]*th)
    acc=(F(0),F(0))
    for k in range(1,kmax+1):
        for a,w in polys[k].items():
            acc=add_interval(acc,scale_interval(w*(-r)**k,(lp[a],hp[a])))
    tail = (6*r)**(kmax+1)/(4*(1-6*r))
    acc = (acc[0]-tail,acc[1]+tail)
    # Q=P/e^u=P/t. Generic interval division by a positive interval.
    vals=[acc[0]/tl,acc[0]/th,acc[1]/tl,acc[1]/th]
    ans=round_interval((min(vals),max(vals)))
    return {"r":str(r),"blocks":kmax,"exp_taylor_terms":exp_terms,
            "lower_fraction":str(ans[0]),"upper_fraction":str(ans[1]),
            "lower_decimal":decimal_string(ans[0]),
            "upper_decimal":decimal_string(ans[1]),
            "width_decimal":decimal_string(ans[1]-ans[0]),
            "P_tail_bound":str(tail),"certification":"exact rational arithmetic"}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=24)
    args=ap.parse_args();n=args.order
    if not 14 <= n <= 60: ap.error('order must lie between 14 and 60')
    out=ROOT/'data';out.mkdir(exist_ok=True)
    polys,c=blocks(n)
    schroeder_check(c)
    u=forward_coefficients(n,lambda j:j*j)
    p,q=inverse_coefficients(polys,n)
    identity=[F(0),F(1)]+[F(0)]*(n-1)
    assert compose(u,q,n)==identity
    assert compose(q,u,n)==identity
    # Independent zero-slope and linear-slope checks.
    u0=forward_coefficients(n,lambda j:0)
    assert all(x==1 for x in u0[1:])
    ul=forward_coefficients(n,lambda j:j)
    # In this case Q(u)=u exp(-u)/(1+u).
    ql=[F(0)]*(n+1)
    for d in range(1,n+1):
        ql[d]=sum((F((-1)**(d-1),math.factorial(m)) for m in range(d)),F(0))
    assert compose(ul,ql,n)==identity
    certs=[certified_Q(F(1,d),polys,14) for d in (20,40,100)]
    with (out/'coefficients.csv').open('w') as f:
        f.write('n,U_n,P_n,Q_n,C_n\n')
        for j in range(1,n+1): f.write(f'{j},{u[j]},{p[j]},{q[j]},{c[j]}\n')
    (out/'quadratic_blocks.json').write_text(json.dumps(
        {str(k):{str(a):str(w) for a,w in polys[k].items()} for k in range(1,n+1)},indent=2))
    (out/'rational_certificates.json').write_text(json.dumps(certs,indent=2))
    # A certified forward inverse value, using Q' >= 619/900 on [-1/20,0].
    # The center is just a chosen rational approximation; its accuracy is not assumed.
    center = -F(2385490927750544, 10**17)
    target = -F(1,40)
    cq = certified_Q(-center, polys, 14, exp_terms=12)
    qlo,qhi = F(cq['lower_fraction']), F(cq['upper_fraction'])
    assert F(certs[0]['upper_fraction']) < target < 0
    residual = max(abs(qlo-target),abs(qhi-target))
    error = F(900,619)*residual
    ulo,uhi = round_interval((center-error,center+error))
    inverse_cert = {"target_q":str(target),"center_u":str(center),
        "Q_center_enclosure":cq,"derivative_lower_bound":"619/900",
        "residual_bound":str(residual),"u_error_bound":str(error),
        "lower_fraction":str(ulo),"upper_fraction":str(uhi),
        "lower_decimal":decimal_string(ulo),"upper_decimal":decimal_string(uhi),
        "width_decimal":decimal_string(uhi-ulo),
        "certification":"exact rational residual transport plus proved derivative bound"}
    (out/'inverse_certificate.json').write_text(json.dumps(inverse_cert,indent=2))
    report={"python":platform.python_version(),"order":n,
            "exact_checks":{"quadratic_U_comp_Q":True,"quadratic_Q_comp_U":True,
                            "Schroeder_recurrence":True,"block_support_and_mass":True,
                            "zero_slopes":True,"linear_slopes":True},
            "certificates":certs,"inverse_certificate":inverse_cert,"first_coefficients":{
                "U":[str(x) for x in u[1:9]],"P":[str(x) for x in p[1:9]],
                "Q":[str(x) for x in q[1:9]]}}
    try:
        import mpmath as mp
        mp.mp.dps=70
        checks=[]
        for rr in (mp.mpf('0.01'),mp.mpf('0.025'),mp.mpf('0.05')):
            def residual(x):
                return sum(x**j*mp.exp(j*j*(-rr)) for j in range(1,180))+rr
            exact=mp.findroot(residual,(-rr,-rr*mp.mpf('1.1')))
            approx=sum((-rr)**k*sum(mp.mpf(w.numerator)/w.denominator*mp.exp(-rr*a)
                        for a,w in polys[k].items()) for k in range(1,n+1))*mp.exp(rr)
            tail=mp.exp(rr)*(6*rr)**(n+1)/(4*(1-6*rr))
            assert abs(exact-approx)<tail
            checks.append({"r":str(rr),"Q_root":mp.nstr(exact,45),
                           "block_error":mp.nstr(abs(exact-approx),12),
                           "analytic_tail_bound":mp.nstr(tail,12)})
        kernel=[]
        for k,a in ((1,0),(2,2),(4,12),(8,56)):
            rr=mp.mpf('0.05')
            def fun(s):
                value=(-s)**k/mp.factorial(k) if a==0 else (-1)**k*(s/a)**(mp.mpf(k)/2)*mp.besselj(k,2*mp.sqrt(a*s))
                return mp.exp(-s/rr)*value/rr
            val=mp.quad(fun,[0,rr,8*rr,mp.inf])
            expected=(-rr)**k*mp.exp(-a*rr)
            assert abs(val-expected)<mp.mpf('1e-60')
            kernel.append({"k":k,"a":a,"absolute_error":mp.nstr(abs(val-expected),5)})
        report['numerical_checks']={"mpmath":mp.__version__,"digits":mp.mp.dps,
            "root_comparisons":checks,"Bessel_Laplace_kernels":kernel,
            "status":"floating-point diagnostics, not interval proofs"}
    except ImportError:
        report['numerical_checks']={"status":"not run: mpmath not installed"}
    (out/'verification.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
