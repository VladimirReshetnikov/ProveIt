"""Exact gap reduction and binomial parity solver for colored double polylogarithms.

Convention: Li_{a,b}(x,y) = sum_{n>m>=1} x**n*y**m/(n**a*m**b).
All symbolic coefficients are integers or fractions; numerical routines are
cross-checks, not certificates. See certify.py for rational interval certificates.
"""
from __future__ import annotations
from functools import lru_cache
from math import comb, factorial
from fractions import Fraction
from typing import Callable


def _indices(a: int, b: int) -> None:
    if isinstance(a, bool) or isinstance(b, bool) or not isinstance(a, int) or not isinstance(b, int) or min(a, b) < 1:
        raise ValueError("a and b must be positive integers")


def correction_coefficients(a: int, b: int) -> dict[int, int]:
    """C_ab = c[0]*Li_w + sum_{j>=2} c[j]*zeta(j)*Li_{w-j}."""
    _indices(a, b)
    w = a+b
    c = {0: (-1)**(b+1)*comb(w-1, b)}
    for j in range(2, b+1):
        c[j] = c.get(j, 0)+(-1)**(b-j)*comb(w-j-1, a-1)
    for j in range(2, a+1):
        c[j] = c.get(j, 0)+(-1)**b*comb(w-j-1, b-1)
    return {j: v for j, v in c.items() if v}


def double_coefficients(a: int, b: int) -> dict[tuple[int, int], int]:
    """Coefficients of F_{w-j,j}(z) in Li_{a,b}(z,z^{-1})."""
    _indices(a, b)
    w = a+b
    return {(w-j, j): (-1)**(b+1)*comb(w-j-1, b-1) for j in range(1, a+1)}


def correction(a: int, b: int, li: Callable, zeta: Callable):
    w = a+b
    return sum(v*li(w) if j == 0 else v*zeta(j)*li(w-j)
               for j, v in correction_coefficients(a, b).items())


def parity_component(a: int, b: int, li: Callable, zeta: Callable,
                     conjugate: Callable, project: Callable):
    """Return Im(F_ab) for even weight, Re(F_ab) for odd weight.

    The caller supplies exact symbolic or numerical single-value operations.
    Arguments are on the unit circle, excluding 1. The projection must match
    the parity of the weight. This routine never evaluates a double sum.
    """
    _indices(a, b)
    w = a+b
    out = 0
    for p in range(1, b+1):
        q = w-p
        cp = correction(p, q, li, zeta)
        cq = correction(q, p, li, zeta)
        r = li(p)*conjugate(li(q))-zeta(w)-cp-conjugate(cq)
        y = project(li(p)*li(q)+(-1)**(q+1)*r)/2
        out += (-1)**(b-p)*comb(w-p-1, b-p)*y
    return out


def u_matrix(w: int) -> list[list[int]]:
    if w < 2: raise ValueError("weight must be at least 2")
    return [[comb(w-j-1, a-j) if j <= a else 0
             for j in range(1, w)] for a in range(1, w)]


def t_matrix(w: int) -> list[list[int]]:
    return [[(-1)**(w-a+1)*v for v in row]
            for a, row in enumerate(u_matrix(w), 1)]


@lru_cache(maxsize=None)
def harmonic(k: int, j: int) -> Fraction:
    return sum((Fraction(1, n**j) for n in range(1, k+1)), Fraction())


def kernel_coefficients(a: int, b: int, k: int) -> dict[int, Fraction]:
    """K_ab(k) = v[0] + sum_{j>=2} v[j]*zeta(j), exactly."""
    _indices(a, b)
    if k < 1: raise ValueError("k must be positive")
    w = a+b
    coeff: dict[int, Fraction] = {0: Fraction()}
    for j in range(2, b+1):
        coeff[j] = coeff.get(j, Fraction())+Fraction((-1)**(b-j)*comb(w-j-1, a-1), k**(w-j))
    for j in range(2, a+1):
        coeff[j] = coeff.get(j, Fraction())+Fraction((-1)**b*comb(w-j-1, b-1), k**(w-j))
    for j in range(1, a+1):
        coeff[0] -= Fraction((-1)**b*comb(w-j-1, b-1), k**(w-j))*harmonic(k, j)
    return {j: v for j, v in coeff.items() if v}


def centered_moments(a: int, b: int, terms: int) -> list[dict[int, Fraction]]:
    """Exact zeta-coordinate vectors of int (t-1/2)^r dmu_ab, 0<=r<terms."""
    if terms < 1: raise ValueError("terms must be positive")
    kernels = [kernel_coefficients(a, b, k+1) for k in range(terms)]
    result = []
    for r in range(terms):
        vec: dict[int, Fraction] = {}
        for k in range(r+1):
            mult = Fraction((-1)**(r-k)*comb(r, k), 2**(r-k))
            for j, v in kernels[k].items():
                vec[j] = vec.get(j, Fraction())+mult*v
        result.append({j: v for j, v in vec.items() if v})
    return result


def _mp_fraction(x: Fraction):
    import mpmath as mp
    return mp.mpf(x.numerator)/x.denominator


def midpoint_value(a: int, b: int, z, terms: int = 180):
    """High-precision estimate and analytic tail bound (roundoff NOT included)."""
    import mpmath as mp
    z = mp.mpc(z)
    q = abs(z)/abs(2-z)
    if q >= 1: raise ValueError("midpoint expansion requires |z| < |2-z|")
    alpha = z/(1-z/2)
    moments = centered_moments(a, b, terms)
    zz = {j: mp.zeta(j) for vec in moments for j in vec if j}
    acc = mp.mpc(0)
    for vec in reversed(moments):
        val = sum(_mp_fraction(v)*(zz[j] if j else 1) for j,v in vec.items())
        acc = val+alpha*acc
    k1 = sum(_mp_fraction(v)*(mp.zeta(j) if j else 1)
             for j,v in kernel_coefficients(a,b,1).items())
    return alpha*acc, abs(alpha)*k1*q**terms/(1-q)


def mixed_integral(a: int, b: int, z):
    """Independent quadrature, not a certified enclosure."""
    import mpmath as mp
    _indices(a, b)
    z = mp.mpc(z)
    return z/factorial(a-1)*mp.quad(
        lambda t: (-mp.log(t))**(a-1)*mp.polylog(b,t)/(1-z*t),
        [0, mp.mpf('0.5'), 1])


def one_variable_integral(a: int, b: int, z):
    """Independent quadrature for F_ab(z)=Li_ab(z,1)."""
    import mpmath as mp
    _indices(a, b)
    z = mp.mpc(z)
    return z/factorial(a-1)*mp.quad(
        lambda t: (-mp.log(t))**(a-1)*mp.polylog(b,z*t)/(1-z*t),
        [0, mp.mpf('0.5'), 1])
