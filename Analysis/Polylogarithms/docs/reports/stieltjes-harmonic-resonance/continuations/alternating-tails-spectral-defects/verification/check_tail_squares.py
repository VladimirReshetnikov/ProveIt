"""Exact certificates and independent analytic diagnostics for tail-square laws.

No numerical diagnostic is an interval certificate.  The exact assertions
use rational/number-field arithmetic.  Infinite numerical sums are checked
with their printed finite-cutoff remainders rather than an unproved tail
extrapolation.  A separate defining-integral diagnostic checks Nielsen beta.
"""

from __future__ import annotations

import json
from math import factorial
from pathlib import Path

import mpmath as mp
import sympy as sp


ROOT = Path(__file__).resolve().parents[1] / "data"


def main() -> None:
    exact = []
    diagnostics = []
    n, p, q, e, lam, t = sp.symbols("n p q e lam t", nonzero=True)
    # p=P(n), q=P(n+1), e=E_n, and lambda^n is represented by h.
    h = sp.symbols("h")
    actual = q * e * (e - lam * h / q) - (e + h / p) * p * e / t
    expected = (q - 1 / t * p) * e**2 - h * (lam + 1 / t) * e
    assert sp.expand(actual - expected) == 0
    exact.append("generic one-step certificate")
    assert sp.expand((actual - (q + lam * p) * e**2).subs(t, -1 / lam)) == 0
    exact.append("compatible-color linear cancellation")
    assert sp.expand((actual - (q + lam * p) * e**2).subs(t, 1 / lam)) != 0
    exact.append("rejected sign-corrupted color")

    k = sp.symbols("k")
    polys = [
        k**2, k**2 - sp.Rational(1, 4), k * (k + 1),
        (k + sp.Rational(1, 3)) * (k + sp.Rational(2, 3)),
        k**4 + 2 * k**2 + 3, (k + 1)**3,
    ]
    colors = [sp.Integer(-1), sp.I, sp.Rational(1, 2)]
    for P in polys:
        for color in colors:
            for K in [1, 3, 7, 12]:
                tails = [sp.S.Zero] * (K + 1)
                for j in range(K - 1, -1, -1):
                    tails[j] = tails[j + 1] + color ** (j + 1) / P.subs(k, j + 1)
                lhs = sum(
                    (-1 / color)**j * (P.subs(k, j + 1) + color * P.subs(k, j))
                    * tails[j]**2 for j in range(K)
                )
                rhs = color * tails[0] * (1 + P.subs(k, 0) * tails[0])
                assert sp.cancel(lhs - rhs) == 0
                exact.append(f"finite K={K}, P={P}, color={color}")

    # The coefficient of x^(2m-4) in the sine-square endpoint.
    x = sp.symbols("x")
    end_series = sp.series((sp.pi**2 / sp.sin(sp.pi*x)**2 - x**-2) / 4, x, 0, 24).removeO().expand()
    for m in range(2, 14):
        claimed = sp.Rational(2*m-3, 2) * sp.zeta(2*m-2)
        assert sp.simplify(end_series.coeff(x, 2*m-4) - claimed) == 0
        exact.append(f"resolvent convolution coefficient m={m}")

    L, u = sp.symbols("L u")
    gammas = sp.symbols("g0:9")
    zseries = 1/u + sum((-1)**j * gammas[j] * u**j / sp.factorial(j) for j in range(9))
    eta = sp.series((1-sp.exp(-L*u))*zseries, u, 0, 9).removeO().expand()
    for r in range(9):
        formula = (-1)**r * (L**(r+1) / (r+1) - sum(sp.binomial(r, j)*L**j*gammas[r-j] for j in range(1, r+1)))
        assert sp.expand(eta.coeff(u, r)*sp.factorial(r) - formula) == 0
        exact.append(f"eta Stieltjes coefficient r={r}")

    mp.mp.dps = 75

    def B(s, z):
        if s == 1:
            return (mp.digamma((z + 1) / 2) - mp.digamma(z / 2)) / 2
        return (mp.zeta(s, z / 2) - mp.zeta(s, (z + 1) / 2)) / 2**s

    def record(name, residual, threshold=mp.mpf("1e-65"), extra=None):
        assert abs(residual) < threshold, (name, residual)
        row = {"name": name, "absolute_residual": mp.nstr(abs(residual), 12), "threshold": str(threshold)}
        if extra:
            row.update(extra)
        diagnostics.append(row)

    cases = [
        (mp.mpf(1), mp.mpf(0)),
        (mp.mpf(2), mp.mpf("0.4")),
        (mp.mpf("3.5"), mp.mpf(0)),
        (mp.mpf("0.5"), mp.mpf("0.3")),
        (mp.mpc("0.7", "0.4"), mp.mpc("0.3", "0.2")),
        (mp.mpc("2.2", "-0.5"), mp.mpf("1.1")),
    ]
    for s, a in cases:
        N = 24
        lhs = mp.fsum(((j+a+1)**s - (j+a)**s) * B(s,j+a+1)**2 for j in range(N+1))
        tail = (N+a+1)**s * B(s,N+a+1)*B(s,N+a+2)
        rhs = B(s,a+1) - a**s*B(s,a+1)**2
        record(f"continuous finite cutoff s={s}, a={a}", lhs + tail - rhs)

    for a, b in [(mp.mpf(0),mp.mpf(1)),(mp.mpf("0.2"),mp.mpf("0.7")),(mp.mpc("0.2","0.3"),mp.mpc("1.1","-0.2"))]:
        N = 36
        M = lambda j: (B(1,j+a+1)-B(1,j+b+1))/(b-a)
        lhs = mp.fsum((2*j+a+b+1)*M(j)**2 for j in range(N+1))
        tail = (N+1+a)*(N+1+b)*M(N)*M(N+1)
        rhs = M(0)-a*b*M(0)**2
        record(f"two-shift cutoff a={a}, b={b}", lhs+tail-rhs)

    for xv in [mp.mpf("0.5"),mp.mpf(1)/3,mp.mpf("0.25"),mp.mpc(0,"0.6"),mp.mpc("0.3","0.2")]:
        N = 40
        E = lambda j: (-1)**(j+1)*(B(1,j+1-xv)-B(1,j+1+xv))/(2*xv)
        lhs = mp.fsum((2*j+1)*E(j)**2 for j in range(N+1))
        boundary = ((N+1)**2-xv**2)*E(N)*E(N+1)
        rhs = mp.pi**2/(4*mp.sin(mp.pi*xv)**2)-1/(4*xv**2)
        record(f"resolvent cutoff x={xv}", lhs-boundary-rhs)

    # Check the B-family against its defining Laplace integral at noninteger
    # and complex orders, independently of its Hurwitz representation.
    for s, z in [(mp.mpf("1.5"),mp.mpf("1.3")),(mp.mpc("1.2","0.3"),mp.mpc("1.1","0.2"))]:
        integ=mp.quad(lambda v: v**(s-1)*mp.exp(-z*v)/(1+mp.exp(-v)),[0,1,mp.inf])/mp.gamma(s)
        record(f"independent Laplace B(s,z), s={s}, z={z}", integ-B(s,z),mp.mpf("1e-60"))

    # All Stieltjes orders are algebraically generated. Check low orders
    # separately using mpmath's generalized Stieltjes evaluator at a few
    # small half-lattice points, and differentiate a finite-cutoff equality.
    log2 = mp.log(2)
    for nv in [0,1,4]:
        for r in range(3):
            C = mp.fsum(mp.binomial(r,j)*log2**(r-j)*(mp.stieltjes(j,mp.mpf(nv+1)/2)-mp.stieltjes(j,mp.mpf(nv+2)/2)) for j in range(r+1))
            # Evaluate the derivative by a Cauchy contour to avoid s=1 poles
            # in numerical finite differences of the Hurwitz representation.
            radius=mp.mpf("0.1")
            terms=128
            jet=mp.fsum(B(1+radius*mp.exp(2j*mp.pi*j/terms),nv+1)*mp.exp(-2j*mp.pi*j*r/terms) for j in range(terms))*mp.factorial(r)/(terms*radius**r)
            record(f"Stieltjes jet n={nv}, r={r}",jet-(-1)**r*C/2,mp.mpf("1e-60"))

    # A direct one-dimensional integral is an independent check of the
    # n=0 starting-index square value sum_{n>=0} B_1(n+1)^2=log 2.
    independent = mp.quad(lambda v:(log2-mp.log(1-v))/(1+v)**2,[0,mp.mpf("0.5"),1])
    record("independent square-sum double-integral reduction",independent-log2)
    for uv in [mp.mpf("0.5"),mp.mpf(1),mp.mpf("1.7")]:
        integ = mp.quad(lambda av:B(1,av+1),[0,uv])
        rhs = mp.log(mp.sqrt(mp.pi)*mp.gamma(1+uv/2)/mp.gamma((1+uv)/2))
        record(f"anchored Gamma integral u={uv}",integ-rhs)

    result = {
        "status": "passed",
        "exact_assertion_count": len(exact),
        "diagnostic_count": len(diagnostics),
        "precision_decimal_digits": mp.mp.dps,
        "exact_assertions": exact,
        "diagnostics": diagnostics,
        "notes": [
            "Finite-cutoff identities include the printed endpoint; finite sums are not presented as uncorrected infinite sums.",
            "Exact arithmetic proves the finite algebraic certificate; analytic statements rest on the accompanying normal-convergence proof.",
            "Floating-point checks are not interval certificates.",
        ],
    }
    (ROOT / "telescoping_verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ["status","exact_assertion_count","diagnostic_count","precision_decimal_digits"]}))


if __name__ == "__main__":
    main()
