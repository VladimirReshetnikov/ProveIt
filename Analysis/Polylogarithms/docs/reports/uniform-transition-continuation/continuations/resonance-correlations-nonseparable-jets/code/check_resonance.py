#!/usr/bin/env python3
"""Independent numerical diagnostics for the resonant Lerch identities.

Numerical residuals are not equality proofs. The article supplies the proofs.
The exact coefficient recurrence is checked separately with SymPy.
Run from any directory; JSON is written to ../data/resonance_checks.json.
"""
from pathlib import Path
import json
import math
import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parents[1] / "data"
OUT.mkdir(exist_ok=True)


def centered_coefficients(k, count):
    b = [mp.mpf(1), mp.mpf(0)] + [mp.mpf(0)] * max(0, count - 1)
    for j in range(2, count + 1):
        b[j] = sum((mp.zeta(r) + (-1)**r * mp.fsum(
            mp.mpf(v)**(-r) for v in range(1, k + 1))) * b[j-r]
            for r in range(2, j + 1)) / j
    return b[:count+1]


def regular_zeta(e, a):
    if e == 0:
        return -mp.digamma(a)
    return mp.zeta(1 + e, a) - 1/e


def exact_pair(k, e, t, a, cutoff=70):
    h = mp.harmonic(k) if k else mp.mpf(0)
    big_t = -mp.log(t) + h - mp.euler
    if e == 0:
        pair = big_t - mp.digamma(a)
    else:
        log_factor = (mp.loggamma(1-e) - mp.fsum(
            mp.log1p(e/j) for j in range(1, k+1)) + e*mp.log(t))
        pair = -mp.expm1(log_factor)/e + regular_zeta(e, a)
    tail = mp.fsum(mp.factorial(k)*(-t)**ell/mp.factorial(k+ell)
                   * mp.zeta(1+e-ell, a) for ell in range(1, cutoff+1))
    return pair + tail


def direct_normalized(k, e, t, a):
    s = k + 1 + e
    f = mp.exp(-a*t) * mp.lerchphi(mp.exp(-t), s, a)
    initial = mp.fsum(mp.zeta(s-j, a)*(-t)**j/mp.factorial(j)
                     for j in range(k))
    return mp.factorial(k)/(-t)**k * (f-initial)


def asymptotic(k, big_t, u, a, order):
    b = centered_coefficients(k, order+1)
    hh = -mp.expm1(-u)/u if u else mp.mpf(1)
    result = big_t*hh - mp.digamma(a)
    for r in range(1, order+1):
        result += (u/big_t)**r * ((-1)**r*mp.stieltjes(r, a)
                  / mp.factorial(r) - mp.exp(-u)*b[r+1])
    return result


def main():
    checks = {"status": "non-interval numerical diagnostics plus exact symbolic recurrences",
              "working_precision": 100, "direct_identity": [],
              "uniform_expansion": [], "finite_part": []}
    mp.mp.dps = 100
    for k, estr, tstr, astr in [
        (0, "0", "0.1", "0.5"), (0, "0.12", "0.4", "1"),
        (1, "-0.13", "0.2", "1.25"), (2, "0", "0.5", "1"),
        (5, "0.11", "0.3", "0.5"), (16, "-0.08", "0.5", "1.25")]:
        e, t, a = map(mp.mpf, (estr, tstr, astr))
        lhs = direct_normalized(k, e, t, a)
        rhs = exact_pair(k, e, t, a, cutoff=100)
        error = abs(lhs-rhs)
        assert error < mp.mpf("1e-65"), (k, error)
        checks["direct_identity"].append({"k": k, "epsilon": estr,
            "t": tstr, "a": astr, "absolute_residual": mp.nstr(error, 12)})
    for k in (0, 1, 5):
        for big_t in (10, 20, 40):
            h = mp.harmonic(k) if k else 0
            t = mp.exp(h-mp.euler-big_t)
            a, u = mp.mpf("0.75"), mp.mpf("1.25")
            exact = exact_pair(k, u/big_t, t, a, cutoff=35)
            approx = asymptotic(k, mp.mpf(big_t), u, a, 3)
            checks["uniform_expansion"].append({"k": k, "T": big_t,
                "u": "1.25", "a": "0.75", "retained_inverse_orders": 3,
                "absolute_error": mp.nstr(abs(exact-approx), 14),
                "T4_scaled_error": mp.nstr(abs(exact-approx)*big_t**4, 14)})
    # Direct exponentially convergent sums, independent of Lerch derivatives.
    for n in (0, 1, 2):
        a, t = mp.mpf("0.75"), mp.mpf("0.4")
        lhs = mp.fsum(mp.exp(-(m+a)*t)*mp.log(m+a)**n/(m+a)
                      for m in range(1000))
        L = -mp.log(t)
        gs = mp.taylor(lambda w: mp.gamma(1-w), 0, n+1)
        poly = (-1)**(n+1)*mp.factorial(n)*mp.fsum(
            gs[j]*(-L)**(n+1-j)/mp.factorial(n+1-j) for j in range(n+2))
        # The native spectral-derivative option avoids an observed loss of
        # accuracy from infinitesimal mp.diff through zeta's s=0 branch.
        tail = mp.fsum((-t)**j/mp.factorial(j)*mp.zeta(
            1-j, a, derivative=n) for j in range(1, 55))
        rhs = poly + mp.stieltjes(n, a) + (-1)**n*tail
        error = abs(lhs-rhs)
        assert error < mp.mpf("1e-55"), (n, error)
        checks["finite_part"].append({"n": n, "a": "0.75", "t": "0.4",
                                      "absolute_residual": mp.nstr(error, 12)})
    # Formal recurrence against exponential coefficient extraction.
    w = sp.Symbol("w")
    c = {r: sp.Symbol(f"c{r}") for r in range(2, 9)}
    b = [sp.Integer(1), sp.Integer(0)]
    for j in range(2, 9):
        b.append(sp.expand(sum(c[r]*b[j-r] for r in range(2, j+1))/j))
    exponential = sp.exp(sum(c[r]*w**r/r for r in range(2, 9))).series(w, 0, 9).removeO()
    assert all(sp.expand(b[j]-exponential.coeff(w,j)) == 0 for j in range(9))
    checks["exact_recurrence"] = {"orders_checked": 8, "passed": True,
                                  "b2": str(b[2]), "b3": str(b[3]), "b4": str(b[4])}
    OUT.joinpath("resonance_checks.json").write_text(json.dumps(checks, indent=2)+"\n")
    print(json.dumps({"direct_identities": len(checks["direct_identity"]),
                      "finite_parts": len(checks["finite_part"]),
                      "asymptotic_samples": len(checks["uniform_expansion"]),
                      "exact_recurrence_order": 8, "status": "passed"}))


if __name__ == "__main__":
    main()
