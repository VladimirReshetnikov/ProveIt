"""Reproducible checks for Herglotz rational jets and large derivative order.

These are floating-point corroborations, not interval proofs.  The article's
Mellin inequalities are the rigorous error bounds.  All displayed rational
coefficients in the finite formula are constructed exactly with SymPy.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


@lru_cache(maxsize=None)
def coefficients(r: int, p: int, q: int):
    return [
        (sp.Rational(a, q) + sp.Rational(b, p), [
            sp.binomial(r, j) * sp.bernoulli(r-j, 1-sp.Rational(b, p))
            - (sp.bernoulli(r, sp.Rational(a, q)) if j == 0 else 0)
            for j in range(r)
        ])
        for a in range(1, q+1) for b in range(p)
    ]


def rational(x):
    return mp.mpf(int(sp.numer(x))) / int(sp.denom(x))


def normalized_jet(r: int, p: int, q: int):
    """D_r(p/q) from the finite Bernoulli--Hurwitz formula."""
    if p == q == 1:
        return mp.mpf(1)/(r*r) + mp.fsum(
            rational(sp.binomial(r, j)*sp.bernoulli(r-j, 1))
            * mp.zeta(r+1-j)/r for j in range(1, r)
        )
    val = mp.mpf(p*q)*(mp.mpf(1)/r-mp.euler-mp.log(q))
    for c, ds in coefficients(r, p, q):
        cm = rational(c)
        val += -mp.digamma(cm) + mp.fsum(
            rational(d)*mp.zeta(r+1-j, cm)
            for j, d in enumerate(ds) if d
        )
    return val/(r*q*q)


def eulerian(m: int):
    a = [1]
    for n in range(1, m+1):
        a = [(k+1)*(a[k] if k < len(a) else 0)
             + (n-k)*(a[k-1] if k else 0) for k in range(n)]
    return a


def normalized_integral(r: int, x):
    """Independent positive real integral, using exact Eulerian coefficients."""
    aa = eulerian(r-1)
    threshold = mp.power(10, -mp.mp.dps/10)

    def kernel(t):
        if t < threshold:
            return mp.mpf('.5') + mp.fsum(
                mp.bernoulli(2*k)*t**(2*k-1)/mp.factorial(2*k)
                for k in range(1, 6)
            )
        return 1/(-mp.expm1(-t))-1/t

    def fun(y):
        if not y:
            return mp.mpf(1)/(2*r)
        z = mp.exp(-y)
        ratio = y/(-mp.expm1(-y))
        return ratio**r * z * mp.polyval(aa[::-1], z) * kernel(y/x) / mp.factorial(r)

    return mp.quad(fun, [0, 1, max(2, r), max(10, 2*r), mp.inf])


def remainder(r: int, x, d):
    return d-mp.zeta(2)-x/r*(mp.log(x)-mp.harmonic(r-1))


def effective_bound(r: int, x, m: int, theta=None, series_factor=None):
    if theta is None:
        theta = mp.pi/4 + mp.mpf(1)/(2*m)
    if series_factor is None:
        series_factor = mp.zeta(m)*mp.zeta(m+1)
    return (2*x*series_factor/(mp.pi*(2*theta-mp.pi/2)*mp.cos(theta))
            * (x/(2*mp.pi*mp.cos(theta)**2))**m
            * mp.gamma(r-m)*mp.gamma(m)*mp.gamma(m+1)/mp.gamma(r+1))


def sigma_minus_one(n: int):
    return mp.fsum(mp.mpf(1)/d for d in range(1, n+1) if n % d == 0)


def u_sum(r: int, x, terms: int):
    return 2*x*mp.fsum(
        sigma_minus_one(n)*mp.re(mp.gamma(r)*mp.hyperu(r, 0, 2j*mp.pi*n/x))
        for n in range(1, terms+1)
    )


def elementary_tail_bound(r: int, x, terms: int):
    """Quarter-plane contour rotation gives |Gamma(r)U(r,0,itau)|<=Gamma(r)/tau**r."""
    factor = (mp.mpf(terms)**(1-r)
              * ((1+mp.log(terms))/(r-1)+mp.mpf(1)/(r-1)**2))
    return 2*x*mp.gamma(r)*(x/(2*mp.pi))**r*factor


def asymptotic(r: int, x):
    tau = 2*mp.pi/x
    amp = (2**mp.mpf('1.25')*mp.pi**mp.mpf('.75')
           * x**mp.mpf('.75') * r**mp.mpf('-.75')
           * mp.exp(-2*mp.sqrt(mp.pi*r/x)))
    phase = 2*mp.sqrt(mp.pi*r/x)-mp.pi/x-mp.pi/8
    kappa = 3/(16*mp.sqrt(tau))+tau**mp.mpf('1.5')/12
    return amp, phase, kappa


def nstr(x, digits=30):
    return mp.nstr(x, digits)


def run(dps: int):
    out = {"working_digits": dps, "status": "floating-point corroboration"}
    mp.mp.dps = dps
    checks = []
    for p, q in [(1,1), (1,2), (2,3), (3,2), (2,5), (3,4), (4,3), (5,2)]:
        for r in [1,2,3,4,6]:
            d = normalized_jet(r, p, q)
            integral = normalized_integral(r, mp.mpf(p)/q)
            residual = abs(d-integral)
            assert residual < mp.power(10, -dps+12), (r,p,q,residual)
            checks.append({"p":p,"q":q,"r":r,"D":nstr(d),"residual":nstr(residual,8)})
    out["finite_formula_checks"] = checks

    exact = []
    for q in [1,2]:
        for r in range(1,7):
            bracket = sp.Rational(q,r)
            for c, ds in coefficients(r,1,q):
                for j, d in enumerate(ds):
                    k = r+1-j
                    hz = (2**k-1)*sp.zeta(k) if c == sp.Rational(1,2) else sp.zeta(k)
                    bracket += d*hz
            value = sp.expand((-1)**(r+1)*sp.factorial(r-1)*q**(r-1)*bracket)
            exact.append({"p":1,"q":q,"r":r,"formula":str(value),"latex":sp.latex(value)})
    out["exact_sample_identities"] = exact

    # Large exact Bernoulli sums need substantially more precision than their
    # final value.  Repeating at 40 extra digits tests for lost-digit artifacts.
    high = []
    for r in [10,20,30,50,80,100,150]:
        work = max(dps, int(r*mp.log10(max(r,3))) + dps)
        with mp.workdps(work):
            d = normalized_jet(r,1,1)
            e = remainder(r,mp.mpf(1),d)
        with mp.workdps(work+40):
            dd = normalized_jet(r,1,1)
            ee = remainder(r,mp.mpf(1),dd)
            assert abs(e-ee) < mp.power(10,-dps), (r,e,ee)
            m = max(2,min(r-1,int(mp.sqrt(mp.pi*r))))
            bound = effective_bound(r,mp.mpf(1),m)
            assert abs(ee) < bound
            amp, phase, kappa = asymptotic(r,mp.mpf(1))
            high.append({"r":r,"work_dps":work,"D":nstr(dd),"E":nstr(ee),
                         "bound":nstr(bound),"m":m,
                         "E_over_amplitude":nstr(ee/amp,20),
                         "leading_cosine":nstr(mp.cos(phase),20),
                         "corrected_cosine":nstr(mp.cos(phase)+kappa/mp.sqrt(r)*mp.cos(phase+mp.pi/4),20)})
    out["large_derivative_checks"] = high

    # Finite arithmetic-sector expansion with the stated analytic tail bound.
    sectors = []
    for p,q,r,terms in [(1,1,12,18), (1,2,14,12), (2,3,16,10)]:
        x = mp.mpf(p)/q
        d = normalized_jet(r,p,q)
        e = remainder(r,x,d)
        partial = u_sum(r,x,terms)
        m = r-2
        # sigma_{-1}(n) <= 1+log n and a decreasing integral comparison.
        factor = mp.mpf(terms)**(1-m)*((1+mp.log(terms))/(m-1)+mp.mpf(1)/(m-1)**2)
        bound = effective_bound(r,x,m,series_factor=factor)
        elementary_bound = elementary_tail_bound(r,x,terms)
        assert abs(e-partial) < bound
        assert abs(e-partial) < elementary_bound
        sectors.append({"p":p,"q":q,"r":r,"terms":terms,"E":nstr(e),
                        "partial":nstr(partial),"absolute_error":nstr(abs(e-partial)),
                        "analytic_tail_bound":nstr(bound),
                        "elementary_tail_bound":nstr(elementary_bound)})
    out["arithmetic_sector_checks"] = sectors

    osc = []
    for x in [mp.mpf('.5'),mp.mpf(1),mp.mpf(2)]:
        for r in [20,50,100,200]:
            first = 2*x*mp.re(mp.gamma(r)*mp.hyperu(r,0,2j*mp.pi/x))
            amp, phase, kappa = asymptotic(r,x)
            corrected = mp.cos(phase)+kappa/mp.sqrt(r)*mp.cos(phase+mp.pi/4)
            osc.append({"x":nstr(x,3),"r":r,"first_sector_over_amplitude":nstr(first/amp,20),
                        "leading_cosine":nstr(mp.cos(phase),20),
                        "corrected_cosine":nstr(corrected,20),
                        "scaled_corrected_error":nstr(r*(first/amp-corrected),20)})
    out["oscillatory_asymptotic_checks"] = osc
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, default=70)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("herglotz_checks.json"))
    args = parser.parse_args()
    report = run(args.dps)
    args.output.write_text(json.dumps(report,indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output":str(args.output),
                      "finite_formula_checks":len(report["finite_formula_checks"]),
                      "large_derivative_checks":len(report["large_derivative_checks"]),
                      "arithmetic_sector_checks":len(report["arithmetic_sector_checks"]),
                      "oscillatory_checks":len(report["oscillatory_asymptotic_checks"])}))
