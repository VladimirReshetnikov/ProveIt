"""Explicit parity reduction of reciprocal-argument double polylogarithms.

Convention: Li_{a,b}(x,y) = sum_{m>n>=1} x**m*y**n/(m**a*n**b).
The theorem applies to a >= 2, b >= 1 and |z| = 1, z != 1.

The accompanying article proves the formula by Fourier coefficients and
bilateral partial fractions. It is a specialization of known depth-two
parity (Nakamura 2012; Panzer 2017, equation (3.2)), not a claim of a new
general parity theorem. Numerical quadrature provides independent checks.

Dependencies: mpmath, sympy. No network access is used.
"""

from __future__ import annotations

from math import comb

import mpmath as mp
import sympy as sp


def _indices(a: int, b: int) -> None:
    if not isinstance(a, int) or not isinstance(b, int) or a < 2 or b < 1:
        raise ValueError("The stated theorem requires integers a >= 2, b >= 1")


def binomial(n: int, k: int) -> int:
    """Binomial coefficient, zero when its lower index is out of range."""
    return comb(n, k) if 0 <= k <= n else 0


def parity_coefficients(a: int, b: int) -> dict:
    """Return the exact integer coefficients in the parity theorem.

    P = Li_b(zbar)*S_a(z) - zeta(w)
        + top*Li_w(zbar)
        + sum coefficient*zeta(even_weight)*Li_polylog_weight(zbar).
    Here S_a(z)=Li_a(z)+(-1)**a*Li_a(zbar), w=a+b.
    """
    _indices(a, b)
    w = a + b
    terms = []
    for s in range(1, max(a, b) // 2 + 1):
        c = binomial(w - 2 * s - 1, a - 1)
        c += binomial(w - 2 * s - 1, b - 1)
        if c:
            terms.append(
                {
                    "even_weight": 2 * s,
                    "polylog_weight": w - 2 * s,
                    "coefficient": -2 * (-1) ** a * c,
                }
            )
    return {"a": a, "b": b, "weight": w, "top": (-1) ** a * comb(w, a),
            "zeta_coefficient": -1, "terms": terms}


def parity_symbolic(a: int, b: int, z=None, zbar=None):
    """Exact symbolic right side, with explicit single polylogarithms."""
    _indices(a, b)
    z = sp.Symbol("z") if z is None else sp.sympify(z)
    zbar = sp.Symbol("zbar") if zbar is None else sp.sympify(zbar)
    data = parity_coefficients(a, b)
    w = a + b
    expr = sp.polylog(b, zbar) * (
        sp.polylog(a, z) + (-1) ** a * sp.polylog(a, zbar)
    )
    expr -= sp.zeta(w)
    expr += data["top"] * sp.polylog(w, zbar)
    for term in data["terms"]:
        expr += term["coefficient"] * sp.zeta(term["even_weight"]) * sp.polylog(
            term["polylog_weight"], zbar
        )
    return sp.expand(expr)


def parity_numeric(a: int, b: int, z):
    """Evaluate the finite parity formula at current mpmath precision.

    The caller supplies a point on the unit circle, different from 1.
    """
    _indices(a, b)
    z = mp.mpc(z)
    if abs(abs(z) - 1) > mp.sqrt(mp.eps) or z == 1:
        raise ValueError("Expected |z| = 1 and z != 1")
    zb = mp.conj(z)
    data = parity_coefficients(a, b)
    w = a + b
    value = mp.polylog(b, zb) * (
        mp.polylog(a, z) + (-1) ** a * mp.polylog(a, zb)
    ) - mp.zeta(w) + data["top"] * mp.polylog(w, zb)
    return value + mp.fsum(
        term["coefficient"] * mp.zeta(term["even_weight"])
        * mp.polylog(term["polylog_weight"], zb)
        for term in data["terms"]
    )


def mixed_integral(a: int, b: int, z):
    """Independent Mellin integral for Li_{a,b}(z,1/z).

    z/(a-1)! * integral_0^1 (-log(t))**(a-1)*Li_b(t)/(1-z*t) dt.
    The numerical integration does not use the parity formula.
    """
    _indices(a, b)
    z = mp.mpc(z)

    def integrand(t):
        if t == 0 or t == 1:
            return mp.mpc(0)
        inner = -mp.log1p(-t) if b == 1 else mp.polylog(b, t)
        return z * (-mp.log(t)) ** (a - 1) * inner / (1 - z * t)

    return mp.quad(integrand, [0, mp.mpf("0.1"), mp.mpf("0.5"),
                               mp.mpf("0.9"), 1]) / mp.factorial(a - 1)


def partial_fraction_symbolic(a: int, b: int, n=None, h=None):
    """Exact rational decomposition used to evaluate the bilateral sum."""
    _indices(a, b)
    n = sp.Symbol("n") if n is None else sp.sympify(n)
    h = sp.Symbol("h", nonzero=True) if h is None else sp.sympify(h)
    w = a + b
    first = sum(
        sp.Integer((-1) ** a * binomial(w - j - 1, b - j))
        / (h ** (w - j) * n ** j) for j in range(1, b + 1)
    )
    second = sum(
        sp.Integer((-1) ** (a - j) * binomial(w - j - 1, a - j))
        / (h ** (w - j) * (n - h) ** j) for j in range(1, a + 1)
    )
    return first + second


def real_single_coefficient(n: int, level: int):
    """Re Li_n(i or rho**2), divided by zeta(n), for n >= 2."""
    if n < 2:
        raise ValueError("This coefficient is for n >= 2")
    if level == 4:
        return -(1 - sp.Rational(2) ** (1 - n)) / 2 ** n
    if level == 3:
        return (sp.Rational(3) ** (1 - n) - 1) / 2
    raise ValueError("Only the manuscript's levels 3 and 4 are implemented")


def imaginary_odd_pi_coefficient(n: int, level: int):
    """Im Li_n(z)/pi**n for n odd; z=i (4) or rho**2 (3)."""
    if n < 1 or n % 2 == 0:
        raise ValueError("n must be positive and odd")
    if level == 4:
        x = sp.Rational(1, 4)
    elif level == 3:
        x = sp.Rational(2, 3)
    else:
        raise ValueError("Only levels 3 and 4 are implemented")
    return sp.simplify(-(2 * sp.I) ** n * sp.bernoulli(n, x)
                       / (2 * sp.I * sp.factorial(n)))


def height_one_exact(a: int, level: int):
    """Exact parity-selected projection at i or rho**2.

    If a is even the return value is Re Li_{a,1}(z,1/z).
    If a is odd it is Im Li_{a,1}(z,1/z).
    beta_s means Im Li_s(i); C_s means Im Li_s(rho), rho=exp(2pi*i/3).
    Only even-index beta_s and C_s remain symbolic.
    """
    _indices(a, 1)
    if level not in (3, 4):
        raise ValueError("Only levels 3 and 4 are implemented")
    ell = sp.log(level if level == 3 else 2) / 2
    if a % 2 == 0:
        m = a // 2
        expr = (sp.Rational(a + 1, 2) * real_single_coefficient(a + 1, level)
                - sp.Rational(1, 2)) * sp.zeta(a + 1)
        expr -= sum(sp.zeta(2 * s) * real_single_coefficient(a + 1 - 2 * s, level)
                    * sp.zeta(a + 1 - 2 * s) for s in range(1, m))
        expr += ell * (1 - real_single_coefficient(a, level)) * sp.zeta(a)
    else:
        m = (a - 1) // 2

        def c(n):
            return sp.Symbol(f"beta_{n}") if level == 4 else -sp.Symbol(f"C_{n}")

        expr = (m + 1) * c(a + 1)
        expr -= sum(sp.zeta(2 * s) * c(a + 1 - 2 * s) for s in range(1, m + 1))
        expr -= ell * imaginary_odd_pi_coefficient(a, level) * sp.pi ** a
    return sp.expand(expr)


def height_one_numeric(a: int, level: int):
    """Evaluate the explicit symbolic height-one projection."""
    expr = height_one_exact(a, level)
    atoms = sorted(expr.free_symbols, key=str)
    vals = []
    for atom in atoms:
        label, index = str(atom).split("_")
        z = mp.j if label == "beta" else mp.exp(2 * mp.pi * mp.j / 3)
        vals.append(mp.im(mp.polylog(int(index), z)))
    return sp.lambdify(atoms, expr, modules="mpmath")(*vals)
