#!/usr/bin/env python3
"""Reproducible checks for Marginal Critical Transseries.

Exact rational/SymPy checks test finite identities. mpmath quadratures and
recurrences are numerical diagnostics, NOT outward-rounded certificates.
Run from the package root: python code/verify.py [--quick]
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from fractions import Fraction
from pathlib import Path
from typing import Any

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def exp_series(f: list[Fraction], order: int) -> list[Fraction]:
    """exp(f), with f[0]=0, in exact rational truncated arithmetic."""
    assert f[0] == 0
    out = [Fraction(0)] * (order + 1)
    out[0] = Fraction(1)
    for k in range(1, order + 1):
        out[k] = sum((j*f[j]*out[k-j] for j in range(1, k+1)), Fraction(0))/k
    return out


def partition_coeff(n: int, beta: Fraction, delta: Fraction, cutoff: int) -> Fraction:
    """Independent multiplicity enumeration of [z^n] exp(n beta F_M(z))."""
    def visit(j: int, left: int) -> Fraction:
        if j > min(n, cutoff):
            return Fraction(int(left == 0))
        a = Fraction(1, j**3) + (delta if j == 1 else 0)
        x = n*beta*a
        return sum((x**k/Fraction(math.factorial(k))*visit(j+1, left-j*k)
                    for k in range(left//j+1)), Fraction(0))
    return visit(1, n)


def exact_checks() -> dict[str, Any]:
    checks = 0
    for beta in [Fraction(1, 3), Fraction(2, 3)]:
        for delta in [Fraction(0), Fraction(1, 2)]:
            for n in range(1, 13):
                for cutoff in [min(3, n), n]:
                    f = [Fraction(0)] + [n*beta*(Fraction(1, j**3)
                         + (delta if j == 1 else 0)) if j <= cutoff else Fraction(0)
                         for j in range(1, n+1)]
                    a = exp_series(f, n)[n]
                    b = partition_coeff(n, beta, delta, cutoff)
                    assert a == b
                    checks += 1
    t, r = sp.symbols("t r")
    V1 = -r/(6*(1-r))
    V2 = r*(1+8*r-5*r**2)/(144*(1-r)**3)
    V3 = -r**2*(9+24*r-31*r**2+10*r**3)/(1296*(1-r)**5)
    h = 1 + V1*t + V2*t*t + V3*t**3
    # The reduced trilogarithm equation through the third t-coefficient.
    expr = h*h-1-2*r*h*h*sp.log(h)+2*r*(t*h**3/6-t*t*h**4/144)
    residual = sp.series(expr, t, 0, 4).removeO().expand()
    for k in range(4):
        assert sp.factor(residual.coeff(t, k)) == 0
        checks += 1
    # The prefix delta=1/2 cancels the cubic term exactly.
    assert Fraction(1, 12)-Fraction(1, 2)/6 == 0
    checks += 1
    # The finite-prefix cancellation in the cutoff correction.
    b, H, ell, gamma = sp.symbols("b H ell gamma", positive=True)
    nu = b+gamma-sp.Rational(3, 2)
    kappa = (2-gamma-sp.log(2)-2*b)/4
    d = nu+sp.log(ell)-sp.log(H)/2
    got = sp.expand(-d/2-1/(2*ell**2)-kappa)
    expected = (sp.log(2)+sp.log(H)-2*sp.log(ell)+1-gamma-2/ell**2)/4
    assert sp.simplify(got-expected) == 0
    checks += 1
    return {"passed": checks, "partition_comparisons": 96,
            "symbolic_reduced_equation_coefficients": 4,
            "cubic_prefix_cancellation": True,
            "prefix_free_cutoff_correction": True}


def power_sums(M: int, degree: int) -> list[int]:
    """Exact sums sum_{j=1}^M j^k, 0<=k<=degree."""
    sums: list[int] = []
    for k in range(degree+1):
        numerator = (M+1)**(k+1)-1
        numerator -= sum(math.comb(k+1, i)*sums[i] for i in range(k))
        val, rem = divmod(numerator, k+1)
        assert rem == 0
        sums.append(val)
    return sums


class Model:
    """a_j=j^-3+delta*1_{j=1}; critical coupling beta=(zeta(2)+delta)^-1."""
    def __init__(self, delta: str = "0") -> None:
        self.delta = mp.mpf(delta)
        self.beta = 1/(mp.zeta(2)+self.delta)
        self.A = self.beta
        self.F1 = mp.zeta(3)+self.delta
        self.b = mp.mpf("1.5")+self.delta
        self.nu = mp.euler+self.delta
        self.c = self.A/2
        self.rcoeff = [mp.mpf(0)]*81
        for k in range(3, 81):
            self.rcoeff[k] = ((-1)**k*mp.zeta(3-k)
                             + self.delta*(-1)**k)/mp.factorial(k)

    def scale(self, n: int) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
        H = -mp.lambertw(-2/(n*self.A), -1).real/2
        B = mp.exp(H)
        return H, B, mp.sqrt(n*self.A)

    def forward_epsilon(self, x: mp.mpf) -> mp.mpf:
        return self.beta*(mp.polylog(3, mp.exp(-x))-mp.zeta(3)
                          +self.delta*mp.expm1(-x)+(mp.zeta(2)+self.delta)*x)

    def inverse_check(self, eps_text: str) -> dict[str, str]:
        eps = mp.mpf(eps_text)
        w = -mp.lambertw(-2*eps/(self.c*mp.exp(2*self.b)), -1).real
        t = mp.sqrt(2*eps/(self.c*w))
        root = mp.findroot(lambda x: self.forward_epsilon(x)-eps, (t*mp.mpf(".99"),t*mp.mpf("1.01")))
        # Pure model displayed formula; prefix models use only the exact core.
        approx = t-t*t/(6*(w-1))+t**3*(w*w+8*w-5)/(144*(w-1)**3)
        return {"epsilon": eps_text, "w": fmt(w), "root": fmt(root),
                "relative_core_error": fmt(abs(t/root-1)),
                "relative_three_term_error": fmt(abs(approx/root-1))}

    def probability(self, n: int, cutoff: int | None = None,
                    lam: str = "0", T: int = 24) -> mp.mpf:
        """Fourier diagnostic. T and internal Taylor truncations are finite."""
        H, B, _ = self.scale(n)
        lamv = mp.mpf(lam)
        beta = self.beta*(1+lamv*B/n)
        if cutoff is None:
            coeff = [n*beta*self.rcoeff[k]*(-mp.j/B)**k for k in range(3,81)]
            def integrand(t: mp.mpf) -> mp.mpf:
                if not t:
                    return mp.mpf(1)
                s = -mp.j*t/B
                analytic = mp.polyval(list(reversed(coeff)), t)*t**3
                exponent = mp.j*lamv*t+n*beta*s*s*(self.b-mp.log(s))/2+analytic
                return mp.exp(exponent).real
        else:
            M = cutoff
            degree = 160
            sums = power_sums(M, degree-3)
            moments = [mp.mpf(0), mp.zeta(2)-mp.zeta(2,M+1)+self.delta,
                       mp.digamma(M+1)+mp.euler+self.delta]
            moments += [mp.mpf(sums[k-3])+self.delta for k in range(3,degree+1)]
            coeff = [mp.mpf(0)]*(degree+1)
            coeff[1] = mp.j*(n*beta*moments[1]-n)/B
            for k in range(2,degree+1):
                coeff[k] = n*beta*moments[k]*(mp.j/B)**k/mp.factorial(k)
            rev = list(reversed(coeff))
            def integrand(t: mp.mpf) -> mp.mpf:
                return mp.exp(mp.polyval(rev,t)).real
        stop = min(mp.mpf(T), mp.pi*B)
        points = [mp.mpf(x) for x in [0, .25, 1, 3, 6, 10, 16] if x < stop]+[stop]
        return mp.quad(integrand, points)/(mp.pi*B)

    def normalized_recurrence(self, n: int, cutoff: int | None = None) -> mp.mpf:
        """Positive coefficient recurrence, normalized by the FULL F(1)."""
        M = min(n, n if cutoff is None else cutoff)
        weights = [mp.mpf(0)]+[1/mp.mpf(j)**2+(self.delta if j==1 else 0)
                             for j in range(1,M+1)]
        p = [mp.exp(-n*self.beta*self.F1)]
        for k in range(1,n+1):
            p.append(n*self.beta/k*mp.fsum(weights[j]*p[k-j]
                                           for j in range(1,min(k,M)+1)))
        return p[n]


def fmt(x: Any, digits: int = 24) -> str:
    return mp.nstr(x, digits)


def run(quick: bool) -> dict[str, Any]:
    mp.mp.dps = 50
    output: dict[str, Any] = {"status":"all assertions passed", "precision_decimal":50,
                             "python":platform.python_version(), "mpmath":mp.__version__,
                             "sympy":sp.__version__, "interval_arithmetic":False}
    output["exact_checks"] = exact_checks()
    pure = Model()
    output["constants"] = {"A":fmt(pure.A), "b":fmt(pure.b)}
    output["inverse"] = [pure.inverse_check(e) for e in ["1e-4","1e-8","1e-16"]]
    # Gaussian-log moments, independently compared with closed formulas.
    phi0 = 1/mp.sqrt(2*mp.pi)
    kap1 = (2-mp.euler-mp.log(2)-2*pure.b)/4
    kap2 = mp.mpf(3)/8*((mp.mpf(4)/3-(mp.euler+mp.log(2))/2-pure.b)**2
                         -mp.pi**2/8-mp.mpf(10)/9)
    g1 = mp.quad(lambda t: mp.exp(-t*t/2)*t*t/2*(mp.log(t)-pure.b),
                 [0,1,3,8,mp.inf])/mp.pi/phi0
    g2 = mp.quad(lambda t: mp.exp(-t*t/2)*t**4/8*((mp.log(t)-pure.b)**2-mp.pi**2/4),
                 [0,1,3,8,mp.inf])/mp.pi/phi0
    assert abs(g1-kap1) < mp.mpf("1e-44")
    assert abs(g2-kap2) < mp.mpf("1e-44")
    output["gaussian_moments"] = {"kappa1":fmt(kap1), "kappa2":fmt(kap2),
                                   "first_difference":fmt(g1-kap1),"second_difference":fmt(g2-kap2)}
    ncheck = 128 if quick else 256
    H,B,N = pure.scale(ncheck)
    M = int(N)
    full_rec = pure.normalized_recurrence(ncheck)
    trunc_rec = pure.normalized_recurrence(ncheck,M)
    full_fourier = pure.probability(ncheck)
    trunc_fourier = mp.exp(-ncheck*pure.A*mp.zeta(3,M+1))*pure.probability(ncheck,M)
    assert abs(full_fourier/full_rec-1) < mp.mpf("1e-18")
    assert abs(trunc_fourier/trunc_rec-1) < mp.mpf("1e-18")
    output["recurrence_vs_fourier"] = {"n":ncheck,"M":M,
                                       "full_relative_difference":fmt(full_fourier/full_rec-1),
                                       "truncated_relative_difference":fmt(trunc_fourier/trunc_rec-1)}
    output["cutoff"] = []
    output["coefficient"] = []
    ns = [10**4, 10**8] if quick else [10**4,10**8,10**16]
    models = [("pure",pure)] if quick else [("pure",pure),("prefix_half",Model("0.5"))]
    for name,model in models:
        for n in ns:
            print(f"Computing {name}, n={n}",flush=True)
            H,B,N = model.scale(n)
            full = model.probability(n)
            k1 = (2-mp.euler-mp.log(2)-2*model.b)/4
            k2 = mp.mpf(3)/8*((mp.mpf(4)/3-(mp.euler+mp.log(2))/2-model.b)**2
                            -mp.pi**2/8-mp.mpf(10)/9)
            output["coefficient"].append({"model":name,"n":n,"H":fmt(H),
                "normalized_coefficient":fmt(full*B/phi0),"two_corrections":fmt(1+k1/H+k2/H**2)})
            for target in ([1] if quick else [0.5,1,2]):
                M = max(1,int(mp.floor(target*N)))
                ell = M/N
                actual = mp.exp(-n*model.A*mp.zeta(3,M+1))*model.probability(n,M)/full
                leading = mp.exp(-1/(2*ell**2))
                C = (mp.log(2*H/ell**2)+1-mp.euler-2/ell**2)/4
                corrected = leading*(1+C/H)
                output["cutoff"].append({"model":name,"n":n,"M":M,"ell":fmt(ell),
                    "actual_ratio":fmt(actual),"leading":fmt(leading),"first_corrected":fmt(corrected),
                    "H_scaled_residual":fmt(H*(actual/leading-1)-C)})
    # A finite-n mathematical bound, evaluated here without directed rounding.
    output["finite_certificate_diagnostics"] = []
    for n in [64,256]:
        H,B,N = pure.scale(n)
        M = min(n,int(mp.ceil(3*N)))
        J = max(1,int(mp.floor(mp.sqrt(n)/mp.log(n+2))))
        delta = mp.mpf(1)
        V = mp.digamma(J+1)+mp.euler
        I = 1/mp.sqrt(2*mp.pi*n*pure.beta*(1-delta**2/12)*V)
        I += mp.exp(-2*n*pure.beta*delta**2/(mp.pi**2*J**2))
        Lambda = n*pure.A/(2*M*M)
        P = pure.normalized_recurrence(n,M)
        lower = P/(P+Lambda*I)
        actual = P/pure.normalized_recurrence(n)
        assert 0 < lower <= actual <= 1
        output["finite_certificate_diagnostics"].append({"n":n,"M":M,"J":J,
            "mathematical_lower_bound_numerical_value":fmt(lower),"actual_ratio_numerical_value":fmt(actual)})
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="smaller diagnostic run")
    args = parser.parse_args()
    DATA.mkdir(exist_ok=True)
    out = run(args.quick)
    name = "verification_quick.json" if args.quick else "verification.json"
    (DATA/name).write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"status":out["status"],"exact_checks":out["exact_checks"],
                      "output":str(DATA/name)},indent=2))


if __name__ == "__main__":
    main()
