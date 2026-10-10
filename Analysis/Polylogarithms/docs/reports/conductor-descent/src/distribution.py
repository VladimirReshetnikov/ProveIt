"""Exact finite-level distribution matrices and a conductor normal form.

All symbols are formal. Matrix rank is NOT numerical independence of periods.
Python 3.10+, SymPy. The public row convention is
    sum_{j=0}^{d-1} e_{b+j*q/d} - weight(d)*e_{d*b},
with e_q the endpoint. Endpoints must not be omitted.
"""
from __future__ import annotations
from math import gcd
from typing import Callable
import sympy as sp
from sympy.polys.matrices import DomainMatrix


def primes(n: int) -> list[int]:
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer")
    return list(sp.factorint(n))


def distribution_matrix(q: int, weight: Callable[[int], object],
                        *, prime_only: bool = True,
                        endpoint: bool = True) -> sp.Matrix:
    if not isinstance(q, int) or q < 2:
        raise ValueError("q must be an integer >= 2")
    ds = primes(q) if prime_only else [d for d in sp.divisors(q) if d > 1]
    rows = []
    for d in ds:
        for b in range(1, q // d + 1):
            row = [sp.S.Zero] * q
            for j in range(d):
                row[b + j * (q // d) - 1] += 1
            row[d * b - 1] -= sp.sympify(weight(d))
            rows.append(row if endpoint else row[:-1])
    return sp.Matrix(rows)


def exact_rank(m: sp.Matrix) -> int:
    """Use exact domain arithmetic (no numerical tolerance)."""
    return DomainMatrix.from_Matrix(m).rank()


def jet_matrix(q: int, w: int, order: int,
               log_value: Callable[[int], object] | None = None,
               *, endpoint: bool = True) -> sp.Matrix:
    """Divided s-derivative jets: coefficient of epsilon**j.

    log_value=None uses independent formal symbols L_p. Evaluating them at
    the actual logarithms gives the analytic jet system. No algebraic
    independence assumption on those logarithms enters the theorem.
    """
    if order < 0:
        raise ValueError("order must be nonnegative")
    if log_value is None:
        log_value = lambda p: sp.Symbol(f"L{p}")
    width = q if endpoint else q - 1
    rows = []
    for n in range(order + 1):
        for p in primes(q):
            for b in range(1, q // p + 1):
                row = [sp.S.Zero] * ((order + 1) * width)
                for j in range(p):
                    a = b + j * (q // p)
                    if endpoint or a < q:
                        row[n * width + a - 1] += 1
                a = p * b
                if endpoint or a < q:
                    for r in range(n + 1):
                        row[(n-r)*width+a-1] -= (
                            sp.Integer(p)**w * log_value(p)**r / sp.factorial(r))
                rows.append(row)
    return sp.Matrix(rows)


def conductor_multiplier(d: int, f: int,
                         character: Callable[[int], object],
                         weight: Callable[[int], object]) -> object:
    """Polynomial A_(d,f,chi) in independent prime weights."""
    if d < 1 or f < 1 or d % f:
        raise ValueError("require positive f dividing d")
    out = sp.S.One
    df = sp.factorint(d)
    ff = sp.factorint(f)
    for p, e in df.items():
        v = ff.get(p, 0)
        t = sp.sympify(weight(p))
        out *= t**(e-v) if v else t**(e-1)*(t-character(p))
    return sp.expand(out)


def q12_normal_form() -> tuple[sp.Matrix, sp.Matrix, tuple]:
    """Rows are e_(a/12), a=1..12. Columns are conductor characters 1,3,4,12.

    The returned B has rows Z_(1,1), Z_(3,chi3), Z_(4,chi4), Z_(12,chi12).
    Exact polynomial identities R*F=0 and B*F=I certify the presentation.
    """
    t2, t3 = sp.symbols("t2 t3")
    chi1 = lambda n: 1
    chi3 = lambda n: 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)
    chi4 = lambda n: 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)
    chi12 = lambda n: chi3(n)*chi4(n)
    chars = [(1, chi1), (3, chi3), (4, chi4), (12, chi12)]
    weight = lambda p: {2:t2, 3:t3}[p]
    F = sp.zeros(12, 4)
    B = sp.zeros(4, 12)
    for a in range(1, 13):
        g = gcd(a, 12); d = 12//g; b = a//g
        for j, (f, chi) in enumerate(chars):
            if d % f == 0:
                F[a-1, j] = conductor_multiplier(d,f,chi,weight)*chi(b)/sp.totient(d)
    for j, (f, chi) in enumerate(chars):
        for a in range(1, f+1):
            if gcd(a, f) == 1:
                B[j, a*(12//f)-1] = chi(a)
    return F, B, (t2, t3)
