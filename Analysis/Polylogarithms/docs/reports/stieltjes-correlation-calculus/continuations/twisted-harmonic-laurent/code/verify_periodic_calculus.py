#!/usr/bin/env python3
"""Independent exact and numerical checks for the periodic finite-part section.

The integral tests use endpoint Taylor subtraction, ordinary quadrature,
and mpmath special functions. They do not evaluate a truncated distribution
Fourier series. Symbolic checks are exact polynomial identities.
"""
from __future__ import annotations

import json
import platform
import sys
from pathlib import Path

import mpmath as mp
import sympy as sp


def exact_checks():
    y = sp.Symbol("y")
    z = {k: sp.Symbol(f"zeta{k}") for k in range(2, 11)}
    b = [sp.Integer(1)]
    for n in range(1, 10):
        b.append(sp.expand((y*b[n-1] + sum(z[j]*b[n-j]
                                         for j in range(2, n+1)))/n))
    T = [sp.expand((-1)**(n+1)*sp.factorial(n)*b[n+1])
         for n in range(8)]
    residuals = {
        "T0*T0": T[0]**2 - (2*T[1]-z[2]),
        "T0*T1": T[0]*T[1] - (sp.Rational(3, 2)*T[2]
                                     -z[2]*T[0]+z[3]),
        "T0*T2": T[0]*T[2] - (sp.Rational(4, 3)*T[3]
                         -2*z[2]*T[1]+2*z[3]*T[0]-2*z[4]),
        "T1*T1": T[1]**2 - (T[3]-2*z[2]*T[1]+2*z[3]*T[0]
                                   +(z[2]**2-3*z[4])/2),
    }
    results = []
    for name, residual in residuals.items():
        value = sp.expand(residual)
        assert value == 0, (name, value)
        results.append({"name": name, "residual": "0"})
    # Reflection uses y_plus=b+i*pi/2 and y_minus=b-i*pi/2.
    br = sp.Symbol("b", real=True)
    yp, ym = br+sp.I*sp.pi/2, br-sp.I*sp.pi/2
    # These are independently expanded reflected Stieltjes products.
    # No Hilbert-transform formula is used in the polynomial checks.
    even_zeta = {z[2]: sp.pi**2/6, z[4]: sp.pi**4/90}
    tp = [sp.expand(t.subs(y, yp).subs(even_zeta)) for t in T]
    tm = [sp.expand(t.subs(y, ym).subs(even_zeta)) for t in T]
    reflected_residuals = {
        "T0*reflected(T1)": tp[0]*tm[1]-(tp[2]/2+tm[2]
                      +sp.pi**2/6*(tp[0]+tm[0])+z[3]),
        "T1*reflected(T1)": tp[1]*tm[1]-(
                      (tp[3]+tm[3])/2+sp.pi**2/3*(tp[1]+tm[1])
                      +z[3]*(tp[0]+tm[0])+sp.Rational(7, 2)*sp.pi**4/90),
    }
    for name, residual in reflected_residuals.items():
        value = sp.expand(residual)
        assert value == 0, (name, value)
        results.append({"name": name, "residual": "0"})
    # Check both frequency signs and the Hilbert convention through
    # eight Taylor coefficients. The reflected phase is exp(-i*pi*v*sign).
    v = sp.Symbol("v")
    for sign in [-1, 1]:
        lhs = sp.exp(-sp.I*sp.pi*v*sign)
        rhs = sp.cos(sp.pi*v)-sp.I*sign*sp.sin(sp.pi*v)
        assert sp.series(lhs-rhs, v, 0, 9).removeO().expand() == 0
    results.append({"name": "reflected generator Hilbert phase through degree 8",
                    "residual": "0", "frequency_signs": 2,
                    "coefficients_per_sign": 9})
    for k in range(8):
        for ell in range(8):
            hk, hl = sp.harmonic(k), sp.harmonic(ell)
            plain = (y-hk)*(y-hl) - (
                2*T[1] + (hk+hl)*T[0]+hk*hl-z[2])
            reflected = (yp-hk)*(ym-hl)-(
                T[1].subs({y: yp, z[2]: sp.pi**2/6})
                +T[1].subs({y: ym, z[2]: sp.pi**2/6})
                +hl*T[0].subs(y, yp)+hk*T[0].subs(y, ym)
                +hk*hl+sp.pi**2/3)
            assert sp.expand(plain) == 0
            assert sp.expand(reflected) == 0
    results.append({"name": "all polygamma products k,l<=7",
                    "residual": "0", "cases": 128})
    # Exact primitive recursion on formal Hurwitz jets. Differentiation
    # sends Z_j(s) to -s Z_j(s+1)-j Z_{j-1}(s+1).
    for n in range(6):
        for q in range(2, 7):
            h = [sp.Integer(1)]
            for degree in range(1, n+2):
                h.append(sp.expand(sum(sp.harmonic(q-1, j)*h[degree-j]
                                       for j in range(1, degree+1))/degree))
            hp = [sp.Integer(1)]
            for degree in range(1, n+2):
                hp.append(sp.expand(sum(sp.harmonic(q-2, j)*hp[degree-j]
                                        for j in range(1, degree+1))/degree))
            c = [(-1)**(n+1)*sp.factorial(n)/sp.factorial(q-1)
                 *h[n+1-j]/sp.factorial(j) for j in range(n+2)]
            cp = [(-1)**(n+1)*sp.factorial(n)/sp.factorial(q-2)
                  *hp[n+1-j]/sp.factorial(j) for j in range(n+2)]
            for j in range(n+2):
                derived = (q-1)*c[j]-(j+1)*(c[j+1] if j+1<len(c) else 0)
                assert sp.simplify(derived-cp[j]) == 0
    results.append({"name": "all repeated primitive recursions n<=5,2<=q<=6",
                    "residual": "0", "cases": 30})
    return results


def numeric_checks(dps=50):
    mp.mp.dps = dps
    rows = []

    def record(name, computed, predicted, **params):
        residual = abs(computed-predicted)
        tolerance = mp.mpf(10)**(-dps+9)*(1+abs(predicted))
        assert residual < tolerance, (name, residual, tolerance)
        rows.append({"name": name, "parameters": params,
                     "computed": mp.nstr(computed, dps),
                     "predicted": mp.nstr(predicted, dps),
                     "absolute_residual": mp.nstr(residual, 12),
                     "tolerance": mp.nstr(tolerance, 12), "passed": True})

    for mode in [1, -2, 3]:
        lam = -2*mp.pi*mp.j*mode
        val = mp.quad(lambda x: mp.digamma(x)*mp.expm1(lam*x), [0, 1])
        target = mp.euler+mp.log(2*mp.pi*mp.j*mode)
        record("P0 test-function finite part", val, target, mode=mode)

    for k in [1, 2, 3]:
        for mode in [1, -2]:
            lam = -2*mp.pi*mp.j*mode
            # exp(lam*x) minus its Taylor polynomial through degree k,
            # divided by x**(k+1), without catastrophic cancellation.
            remainder = mp.quad(lambda x: lam**(k+1)/mp.factorial(k+1)
                        *mp.hyp1f1(1, k+2, lam*x), [0, 1])
            correction = sum(lam**j/(mp.factorial(j)*(j-k)) for j in range(k))
            regular = mp.quad(lambda x: mp.zeta(k+1, 1+x)*mp.exp(lam*x), [0, 1])
            val = (-1)**(k+1)*mp.factorial(k)*(remainder+correction+regular)
            target = (2*mp.pi*mp.j*mode)**k*(
                mp.euler+mp.log(2*mp.pi*mp.j*mode)-mp.harmonic(k))
            record("Pk test-function finite part", val, target, k=k, mode=mode)

    for atext in ["0.3", "0.5", "0.77"]:
        a = mp.mpf(atext)
        pa = mp.digamma(a)

        def integrand(x):
            if x == 0 or x == a:
                return mp.polygamma(1, a)-mp.euler*pa+pa/a
            return mp.digamma(x)*mp.digamma(a-x)+pa*(1/x+1/(a-x))

        val = (mp.quad(integrand, [0, a/2, a])
               +mp.quad(lambda x: mp.digamma(x)*mp.digamma(1+a-x), [a, 1])
               -2*pa*mp.log(a))
        target = 2*mp.stieltjes(1, a)+mp.zeta(2)
        record("convergent digamma convolution", val, target, a=atext)

        g = lambda x: mp.loggamma(x)-mp.log(2*mp.pi)/2
        val = mp.quad(lambda x: g(x)*g(a-x), [0, a/2, a])
        val += mp.quad(lambda x: g(x)*g(1+a-x), [a, 1])
        target = (mp.diff(lambda s: mp.zeta(s, a), -1, 2)
                  +2*mp.diff(lambda s: mp.zeta(s, a), -1)
                  +(2-mp.zeta(2))*mp.zeta(-1, a))
        record("ordinary centered log-Gamma convolution", val, target, a=atext)
    return rows


def main():
    output = Path(sys.argv[1]) if len(sys.argv)>1 else (
        Path(__file__).resolve().parents[1]/"data"/"periodic_calculus_checks.json")
    report = {"purpose": "Independent tests of finite-part normalization and exact identities",
              "python": platform.python_version(), "mpmath": mp.__version__,
              "sympy": sp.__version__, "working_decimal_precision": 50,
              "symbolic": exact_checks(), "numerical": numeric_checks()}
    report["passed"] = True
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"passed": True, "symbolic_groups": len(report["symbolic"]),
                      "numerical_cases": len(report["numerical"]), "output": str(output)}))


if __name__ == "__main__":
    main()
