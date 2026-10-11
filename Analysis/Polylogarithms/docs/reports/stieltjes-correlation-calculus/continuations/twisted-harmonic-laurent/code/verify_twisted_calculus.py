#!/usr/bin/env python3
"""Checks of the twisted Lerch finite-part normalization.

The Fourier tests integrate endpoint-subtracted ordinary functions.  In
particular, the zero-mode tests distinguish the unit delta from delta-1
and detect omitted covariant contact terms.  Rational-function checks
compare Lerch evaluations with separate Hurwitz/Stieltjes/polygamma
formulas.  Symbolic coefficient tests are exact; numerical residuals are
diagnostics, not proof.
"""
from __future__ import annotations

import json
import platform
import sys
from pathlib import Path

import mpmath as mp
import sympy as sp


def symbolic_checks():
    y, u = sp.symbols("y u")
    zeta = {j: sp.Symbol(f"zeta{j}") for j in range(2, 10)}
    degree = 8
    b = [sp.Integer(1)]
    for n in range(1, degree + 1):
        b.append(sp.expand((y * b[n-1] + sum(
            zeta[j] * b[n-j] for j in range(2, n+1))) / n))

    # Independently form the bivariate Gamma quotient by exponentiating
    # log C = sum zeta(r)/r * (u^r+v^r-(u+v)^r), retaining u,v<=4.
    cap = 4
    log_c = {}
    for r in range(2, degree + 1):
        for i in range(1, r):
            j = r-i
            if i <= cap and j <= cap:
                log_c[i, j] = -zeta[r]*sp.binomial(r, i)/r

    def multiply(a, b):
        out = {}
        for (i, j), av in a.items():
            for (k, ell), bv in b.items():
                ij = (i+k, j+ell)
                if ij[0] <= cap and ij[1] <= cap:
                    out[ij] = out.get(ij, 0) + av*bv
        return {ij: sp.expand(v) for ij, v in out.items()}

    c = {(0, 0): sp.Integer(1)}
    power = {(0, 0): sp.Integer(1)}
    for r in range(1, cap+1):
        power = multiply(power, log_c)
        for ij, val in power.items():
            c[ij] = sp.expand(c.get(ij, 0) + val/sp.factorial(r))

    buv = {(i, j): b[i+j]*sp.binomial(i+j, i)
           for i in range(cap+1) for j in range(cap+1)}
    predicted = multiply(c, buv)
    for m in range(4):
        for n in range(4):
            assert sp.expand(predicted[m+1, n+1]-b[m+1]*b[n+1]) == 0
    groups = [{"name": "all-index Gamma-quotient table through m,n=3",
               "cases": 16, "residual": "0",
               "includes_constant_contact_coefficient": True}]

    # At every (including zero) twisted frequency, the exact Gamma
    # recurrence gives exp(y*u)/prod(1+u/j).  Its finite Laurent term
    # is y-H_k, hence the covariant correction H_k*lambda^k*delta.
    for k in range(9):
        factor = sp.prod(1+u/sp.Integer(j) for j in range(1, k+1))
        coefficient = sp.diff(sp.exp(y*u)/factor, u).subs(u, 0)
        assert sp.simplify(coefficient-(y-sp.harmonic(k))) == 0
    groups.append({"name": "finite Laurent coefficient and harmonic contact",
                   "cases": 9, "residual": "0"})

    mode = sp.Symbol("n", integer=True)
    shifted = mode+sp.Rational(1, 2)
    reflected = (-mode-1)+sp.Rational(1, 2)
    assert sp.expand(shifted+reflected) == 0
    assert -(-mode-1)-1 == mode
    groups.append({"name": "half-twist modulated reflection and involution",
                   "cases": 2, "residual": "0"})
    return groups


def numerical_checks(dps=60):
    mp.mp.dps = dps
    rows = []

    def record(name, computed, expected, **parameters):
        residual = abs(computed-expected)
        scaled = residual/(1+abs(expected))
        tolerance = mp.mpf(10)**(-dps+10)
        assert scaled < tolerance, (name, parameters, scaled, tolerance)
        rows.append({
            "name": name, "parameters": parameters,
            "computed": mp.nstr(computed, dps),
            "expected": mp.nstr(expected, dps),
            "absolute_residual": mp.nstr(residual, 15),
            "scaled_residual": mp.nstr(scaled, 15),
            "scaled_tolerance": mp.nstr(tolerance, 5),
            "passed": True,
        })

    def nielsen_beta(x):
        return (mp.digamma((x+1)/2)-mp.digamma(x/2))/2

    def euler_zeta(s, x):
        return (mp.zeta(s, x/2)-mp.zeta(s, (x+1)/2))*2**(-s)

    # Raw cutoff Fourier coefficients of the first Lerch jet.  The
    # recurrence beta(x)=1/x-beta(x+1) cancels its endpoint singularity.
    for mode in [-2, -1, 0, 1, 2]:
        lam = -2*mp.pi*mp.j*(mode+mp.mpf("0.5"))

        def integrand(x):
            if not x:
                return lam-mp.log(2)
            return mp.expm1(lam*x)/x-mp.exp(lam*x)*nielsen_beta(x+1)

        computed = mp.quad(integrand, [0, 1])
        expected = -mp.euler-mp.log(-lam)
        record("half-twist U0 finite-part Fourier coefficient",
               computed, expected, mode=mode)

    # Higher finite parts use the exact exponential Taylor remainder.
    # The smooth Euler-zeta tail has the opposite sign to the ordinary
    # Hurwitz tail; the Fourier phase contains n+1/2, not n.
    for k in [1, 2, 3]:
        for mode in [-1, 0, 2]:
            lam = -2*mp.pi*mp.j*(mode+mp.mpf("0.5"))
            remainder = mp.quad(
                lambda x: lam**(k+1)/mp.factorial(k+1)
                *mp.hyp1f1(1, k+2, lam*x), [0, 1])
            monomials = sum(lam**j/(mp.factorial(j)*(j-k))
                            for j in range(k))
            smooth = mp.quad(
                lambda x: mp.exp(lam*x)*euler_zeta(k+1, x+1), [0, 1])
            computed = (-1)**(k+1)*mp.factorial(k)*(
                remainder+monomials-smooth)
            expected = (-lam)**k*(mp.euler+mp.log(-lam)-mp.harmonic(k))
            record("half-twist Pk raw finite-part Fourier coefficient",
                   computed, expected, k=k, mode=mode)

    x = mp.mpf("0.37")
    # Direct Lerch evaluation vs rational Hurwitz decomposition at
    # nonintegral complex order (avoids all resonance expansions).
    s = mp.mpc("0.7", "0.4")
    for p, q in [(1, 2), (1, 3), (2, 5)]:
        theta = mp.mpf(p)/q
        z = mp.exp(-2*mp.pi*mp.j*theta)
        phase = mp.exp(-2*mp.pi*mp.j*theta*x)
        computed = phase*mp.lerchphi(z, s, x)
        expected = phase*q**(-s)*sum(
            z**r*mp.zeta(s, (x+r)/q) for r in range(q))
        record("rational Lerch-Hurwitz reduction",
               computed, expected, p=p, q=q, x=str(x), order=str(s))

    # Taylor jets at s=1: direct Lerch differentiation and ordinary
    # generalized Stieltjes constants are evaluated independently.
    for p, q in [(1, 2), (1, 3)]:
        theta = mp.mpf(p)/q
        z = mp.exp(-2*mp.pi*mp.j*theta)
        phase = mp.exp(-2*mp.pi*mp.j*theta*x)
        for n in range(3):
            computed = phase*(-1)**n*mp.diff(
                lambda order: mp.lerchphi(z, order, x), 1, n)
            expected = phase/q*sum(
                z**r*sum(mp.binomial(n, j)*mp.log(q)**(n-j)
                         *mp.stieltjes(j, (x+r)/q) for j in range(n+1))
                for r in range(q))
            record("rational Lerch-Stieltjes jet",
                   computed, expected, p=p, q=q, x=str(x), jet=n)

    for p, q in [(1, 2), (1, 3), (2, 5)]:
        theta = mp.mpf(p)/q
        z = mp.exp(-2*mp.pi*mp.j*theta)
        phase = mp.exp(-2*mp.pi*mp.j*theta*x)
        for k in range(3):
            computed = ((-1)**(k+1)*mp.factorial(k)*phase
                        *mp.lerchphi(z, k+1, x))
            expected = phase/q**(k+1)*sum(
                z**r*mp.polygamma(k, (x+r)/q) for r in range(q))
            record("rational twisted polygamma including k=0",
                   computed, expected, p=p, q=q, x=str(x), k=k)
    return rows


def main():
    output = Path(sys.argv[1]) if len(sys.argv) > 1 else (
        Path(__file__).resolve().parents[1]/"data"/"twisted_calculus_checks.json")
    report = {
        "purpose": "Independent twisted finite-part, unit, and rational-jet checks",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "sympy": sp.__version__, "working_decimal_precision": 60,
        "symbolic": symbolic_checks(), "numerical": numerical_checks(),
        "passed": True,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "passed": True, "symbolic_groups": len(report["symbolic"]),
        "symbolic_cases": sum(g["cases"] for g in report["symbolic"]),
        "numerical_cases": len(report["numerical"]),
        "maximum_scaled_residual": max(
            (r["scaled_residual"] for r in report["numerical"]),
            key=mp.mpf),
        "output": str(output),
    }))


if __name__ == "__main__":
    main()
