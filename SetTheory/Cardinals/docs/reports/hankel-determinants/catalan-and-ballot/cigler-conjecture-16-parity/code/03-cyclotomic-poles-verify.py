#!/usr/bin/env python3
"""Reproduce exact checks accompanying the cyclotomic pole-collapse article.

Run from any working directory: python /path/to/package/code/verify.py
Requires SymPy 1.14.0 (the delivered run used Python 3.13.5).

Finite checks are NOT a proof of the general theorems. In particular, the
finite-field experiments are not a characteristic-zero proof. The article
supplies the all-index arguments. No checks depend on floating-point values.
"""
from __future__ import annotations
import itertools
import json
import math
from pathlib import Path
import platform
import sys
import time
import traceback
from datetime import datetime, timezone
import sympy as sp
from modular import (berlekamp_massey, phase_multiplicities,
                     predicted_exponents, schur_sequence_mod)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
n, x = sp.symbols("n x")


def require(condition: bool, message: str) -> None:
    """Checks remain active under Python's -O option."""
    if not condition:
        raise AssertionError(message)


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def factorial_ratio(m: int, r: int) -> sp.Rational:
    return sp.Rational(math.prod(math.factorial(j) for j in range(r)),
                       math.prod(math.factorial(j) for j in range(m - r, m)))


def canonical_polynomials(nodes: list[sp.Expr], mult: list[int],
                          height: int) -> dict[tuple[int, ...], sp.Poly]:
    """Confluent Laplace expansion, independent of the proposed jet formulas."""
    K, A = sum(mult), height
    C = K - A
    rows = [(node, h, i) for i, (node, m) in enumerate(zip(nodes, mult))
            for h in range(m)]
    low = sp.Matrix([[sp.binomial(j, h) * node ** (j - h) for j in range(C)]
                     for node, h, i in rows])
    high = sp.Matrix([[
        sp.sympify(sp.prod(n + C + j - u for u in range(h)))
        / math.factorial(h) * node ** (C + j - h) for j in range(A)]
        for node, h, i in rows])
    delta = sp.prod((nodes[j] - nodes[i]) ** (mult[i] * mult[j])
                    for i in range(len(nodes)) for j in range(i + 1, len(nodes)))
    result: dict[tuple[int, ...], sp.Expr] = {}
    for selected in itertools.combinations(range(K), A):
        remaining = [j for j in range(K) if j not in selected]
        sign = (-1) ** sum(i < j for i in selected for j in remaining)
        allocation = tuple(sum(rows[j][2] == i for j in selected)
                           for i in range(len(nodes)))
        term = sign * low[remaining, :].det() * high[list(selected), :].det() / delta
        result[allocation] = result.get(allocation, sp.Integer(0)) + term
    return {r: sp.Poly(sp.expand(value), n) for r, value in result.items()}


def expected_jet(nodes: list[sp.Expr], mult: list[int], allocation: tuple[int, ...]
                 ) -> tuple[int, sp.Expr, sp.Expr]:
    L = len(nodes)
    r = allocation
    s = [mult[i] - r[i] for i in range(L)]
    d = [r[i] * s[i] for i in range(L)]
    leading = sp.prod(factorial_ratio(mult[i], r[i]) for i in range(L)) * sp.prod(
        (1 - nodes[j] / nodes[i]) ** (-r[i] * s[j])
        for i in range(L) for j in range(L) if i != j)
    centered = sp.Rational(1, 2) * sum(
        (d[i] * (2 * r[j] - mult[j]) - d[j] * (2 * r[i] - mult[i]))
        * (nodes[i] + nodes[j]) / (nodes[i] - nodes[j])
        for i in range(L) for j in range(i + 1, L))
    return sum(d), sp.simplify(leading), sp.simplify(centered)


def verify_canonical() -> dict:
    modes = 0
    for k in range(2, 8):
        a, b, M = k // 2, (k - 1) // 2, k - 1
        for t0 in (2, 3):
            t = sp.Integer(t0)
            nodes, mult = [sp.Integer(1), t, t*t], [a, 1, b]
            polynomials = canonical_polynomials(nodes, mult, a)
            by_q = {r[1] + 2*r[2]: p for r, p in polynomials.items()}
            for r, polynomial in polynomials.items():
                q = r[1] + 2*r[2]
                D, leading, centered = expected_jet(nodes, mult, r)
                tag = f"canonical k={k}, t={t0}, q={q}"
                require(polynomial.degree() == D and polynomial.LC() == leading,
                        tag + " degree/leading mismatch")
                p_center = sp.Poly(polynomial.as_expr().subs(n, x-sp.Rational(k, 2)), x)
                if D:
                    require(sp.simplify(p_center.nth(D-1)/leading-centered) == 0,
                            tag + " centered coefficient mismatch")
                prefactor = ((-1)**a * t**(a*(M-2*q)) if k % 2 == 0
                             else t**(k*(a-q)))
                reflected = prefactor * polynomial.as_expr().subs(n, -n-k)
                require(sp.expand(by_q[M-q].as_expr()-reflected) == 0,
                        tag + " reflection mismatch")
                modes += 1
    general_modes = 0
    for mult, A in [([2, 2], 2), ([2, 2, 2], 2), ([2, 2, 2], 3), ([3, 2, 1], 3)]:
        nodes = [sp.Integer(v) for v in [2, 3, 5][:len(mult)]]
        for r, polynomial in canonical_polynomials(nodes, mult, A).items():
            D, leading, centered = expected_jet(nodes, mult, r)
            require(polynomial.degree() == D and polynomial.LC() == leading,
                    f"general cluster degree/leading mismatch {mult}, {A}, {r}")
            p_center = sp.Poly(polynomial.as_expr().subs(n, x-sp.Rational(sum(mult), 2)), x)
            if D:
                require(sp.simplify(p_center.nth(D-1)/leading-centered) == 0,
                        f"general cluster jet mismatch {mult}, {A}, {r}")
            general_modes += 1
    return {"cigler_modes": modes, "k_range": [2, 7], "parameters": [2, 3],
            "additional_general_cluster_modes": general_modes,
            "arithmetic": "exact rational polynomials", "passed": True}


def schur_exact(k: int, t: sp.Expr, count: int) -> list[sp.Expr]:
    a, b = k//2, (k-1)//2
    complete = [sp.Integer(0)]*(count+a+1)
    complete[0] = sp.Integer(1)
    for node in [sp.Integer(1)]*a + [t] + [t*t]*b:
        for j in range(1, len(complete)):
            complete[j] = sp.expand(complete[j] + node*complete[j-1])
    result = []
    for nn in range(count):
        mat = sp.Matrix([[complete[nn-i+j] if nn-i+j >= 0 else 0
                          for j in range(a)] for i in range(a)])
        result.append(sp.expand(mat.det(method="domain-ge")))
    return result


def alpha(s: int, L: int) -> sp.Expr:
    return sp.prod(sp.Rational(2*L+u+v-1, u+v-1)
                   for u in range(1, s) for v in range(u, s))


def beta(s: int, L: int) -> sp.Expr:
    return sp.prod(sp.Rational(2*L+u+v, u+v)
                   for u in range(1, s) for v in range(u, s))


def fourth_product(m: int, nn: int) -> sp.Expr:
    L, residue = divmod(nn, 4)
    if residue == 0:
        return alpha(m+1, L)*beta(m, L)**2*beta(m+1, L)
    if residue == 1:
        return (-1)**m*2*alpha(m, L+1)*beta(m, L)*beta(m+1, L)**2
    if residue == 2:
        return 2*alpha(m, L+1)*beta(m, L+1)*beta(m+1, L)**2
    return (-1)**m*alpha(m+1, L+1)*beta(m, L+1)**2*beta(m+1, L)


def verify_fourth_products() -> dict:
    count = 0
    for m in range(1, 5):
        for nn, value in enumerate(schur_exact(4*m+1, sp.I, 20)):
            require(value == fourth_product(m, nn), f"fourth product mismatch m={m}, n={nn}")
            count += 1
    return {"count": count, "m_range": [1, 4], "n_range": [0, 19],
            "arithmetic": "exact Gaussian-rational determinants", "passed": True}


def verify_symbolic_power_sums() -> dict:
    m, u, v = sp.symbols("m u v", integer=True, positive=True)
    center = 2*m + sp.Rational(1, 2)

    def triangular(s: sp.Expr, offset: int, degree: int) -> sp.Expr:
        polynomial = sp.Poly(sp.expand((2*(u+v)+offset-center)**degree), u, v)
        total = sp.Integer(0)
        for (i, j), coefficient in polynomial.terms():
            inner = sp.summation(u**i, (u, 1, v))
            total += coefficient*sp.summation(sp.expand(v**j*inner), (v, 1, s))
        return sp.factor(total)

    p0, p1 = [None], [None]
    differences = [None, 0, 2*m, 3*m*m, m*(16*m*m-11),
                   sp.Rational(5, 2)*m*m*(8*m*m-5)]
    for j in range(1, 6):
        p0.append(sp.factor(triangular(m, -2, j)+2*triangular(m-1, 0, j)
                            +triangular(m, 0, j)))
        p1.append(sp.factor(triangular(m-1, 1, j)+triangular(m-1, -1, j)
                            +2*triangular(m, -1, j)))
        require(sp.expand(p0[j]-p1[j]-differences[j]) == 0,
                f"symbolic power-sum difference {j} failed")
    require(sp.expand(p0[1]-m) == 0, "common first power sum failed")
    require(sp.expand((p0[2]+p1[2])/2-m*m*(8*m*m+1)/6) == 0,
            "average second power sum failed")
    require(sp.expand((p0[3]+p1[3])/2-m*(16*m*m-9)/4) == 0,
            "average third power sum failed")

    def newton(p: list) -> list:
        e = [sp.Integer(1)]
        for j in range(1, 6):
            e.append(sp.factor(sum((-1)**(h-1)*e[j-h]*p[h]
                                   for h in range(1, j+1))/j))
        return e
    e0, e1 = newton(p0), newton(p1)
    for j, expected in [(1, 0), (3, 0), (5, -m*m*(m*m-1))]:
        require(sp.expand(e0[j]-e1[j]-expected) == 0,
                f"symbolic elementary difference {j} failed")
    return {"symbolic_variable": "m", "power_sum_degrees": [1, 2, 3, 4, 5],
            "elementary_differences": {str(j): str(sp.factor(e0[j]-e1[j])) for j in [1, 3, 5]},
            "passed": True}


def moment(r: int, t: sp.Expr) -> sp.Expr:
    if r == 0:
        return sp.Integer(1)
    return sp.expand(sum(sp.binomial((r-1)//2, (j-1)//2)
                         *sp.binomial(r//2, j//2)*t**(j-1) for j in range(1, r+1)))


def verify_hankel_interface() -> dict:
    count = 0
    for k in range(1, 9):
        for t in [sp.Integer(2), sp.Integer(-2), sp.I]:
            schur = schur_exact(k, t, 6)
            moments = [moment(r, t) for r in range(k+9)]
            for nn in range(6):
                mat = sp.Matrix([[moments[k+i+j] for j in range(nn)] for i in range(nn)])
                determinant = mat.det(method="domain-ge")
                exponent = nn*(nn-1)//2
                normalized = sp.expand((-1)**(k*exponent)*t**(-exponent)*determinant)
                require(sp.simplify(normalized-schur[nn]) == 0,
                        f"Hankel/Schur mismatch k={k}, n={nn}, t={t}")
                count += 1
    return {"count": count, "k_range": [1, 8], "n_range": [0, 5],
            "parameters": ["2", "-2", "i"], "passed": True}


def verify_modular() -> dict:
    records = []
    for ell in range(3, 18):
        prime = ell*((1_000_000+ell-1)//ell)+1
        while not sp.isprime(prime):
            prime += ell
        root = pow(int(sp.primitive_root(prime)), (prime-1)//ell, prime)
        require(pow(root, ell, prime) == 1 and all(
            pow(root, d, prime) != 1 for d in sp.divisors(ell) if d < ell),
            "primitive-root construction failed")
        for k in range(2, 18):
            predicted = predicted_exponents(k, ell)
            baseline = [max([1+q*(k-1-q)//2 for q in range(r, k, ell)], default=0)
                        for r in range(ell)]
            count = 2*sum(baseline)+8
            sequence = schur_sequence_mod(k, root, prime, count)
            connection = berlekamp_massey(sequence, prime)
            actual, remainder = phase_multiplicities(connection, root, ell, prime)
            require(actual == predicted and remainder == [1],
                    f"modular multiplicities mismatch k={k}, ell={ell}, p={prime}")
            order = len(connection)-1
            require(all((sequence[nn]+sum(connection[j]*sequence[nn-j]
                    for j in range(1, order+1))) % prime == 0
                    for nn in range(order, count)), "connection-prefix residual failed")
            records.append({"k": k, "cyclotomic_order": ell, "prime": prime,
                            "root": root, "terms": count, "exponents": actual,
                            "recurrence_order": order})
    atomic_json(DATA / "modular_checks.json", records)
    return {"count": len(records), "k_range": [2, 17], "ell_range": [3, 17],
            "arithmetic": "exact finite fields, deterministic primes above 10^6",
            "limitation": "finite-field finite-prefix checks, not an all-index characteristic-zero proof",
            "passed": True}


def main() -> int:
    DATA.mkdir(parents=True, exist_ok=True)
    report = {"status": "running", "utc": datetime.now(timezone.utc).isoformat(),
              "python": platform.python_version(), "sympy": sp.__version__,
              "scope": "regression evidence; the mathematical proofs are in article.pdf",
              "checks": {}}
    started = time.perf_counter()
    try:
        for name, function in [("canonical_coefficients", verify_canonical),
                               ("fourth_root_products", verify_fourth_products),
                               ("symbolic_cancellation", verify_symbolic_power_sums),
                               ("hankel_schur_interface", verify_hankel_interface),
                               ("modular_recurrences", verify_modular)]:
            report["checks"][name] = function()
            print(f"PASS {name}: {report['checks'][name]}", flush=True)
        report["status"] = "passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
        traceback.print_exc()
    report["elapsed_seconds"] = round(time.perf_counter()-started, 3)
    atomic_json(DATA / "verification.json", report)
    print(f"{report['status'].upper()}: {DATA / 'verification.json'}", flush=True)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
