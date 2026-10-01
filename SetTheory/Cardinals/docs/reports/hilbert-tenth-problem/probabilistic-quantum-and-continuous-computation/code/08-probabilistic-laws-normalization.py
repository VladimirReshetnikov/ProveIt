"""Exact optimal normalization budgets and their single-fold quartic certificates.

All arithmetic in certificate generation is integer or Fraction arithmetic.
The optional symbolic compiler requires SymPy.  Indices in code are zero-based.
A schedule has N+1 strictly positive integer rows; each row is divided by its sum.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence, Any


def validate(rows: Sequence[Sequence[int]], alpha: int, beta: int) -> None:
    if not rows or len(rows[0]) < 2:
        raise ValueError("At least one row and two outcome labels are required")
    m = len(rows[0])
    if any(len(r) != m for r in rows):
        raise ValueError("All rows must have the same length")
    if any(type(x) is not int or x < 1 for r in rows for x in r):
        raise ValueError("Row entries must be strictly positive integers")
    if type(alpha) is not int or type(beta) is not int or not 1 <= alpha <= beta:
        raise ValueError("Require integers 1 <= alpha <= beta")


def optimal_budget(rows: Sequence[Sequence[int]]) -> tuple[Fraction, list[int], list[Fraction]]:
    """Return maximum feasible initial mass, canonical pivots, and step factors."""
    validate(rows, 1, 1)
    ps = [[Fraction(x, sum(r)) for x in r] for r in rows]
    product = Fraction(1)
    pivots, factors = [], []
    for old, new in zip(ps, ps[1:]):
        ratios = [x / y for x, y in zip(old, new)]
        largest = max(ratios)
        pivots.append(ratios.index(largest))
        factors.append(largest)
        product *= largest
    return 1 / product, pivots, factors


def make_assignment(rows: Sequence[Sequence[int]], alpha: int, beta: int,
                    pivots: Sequence[int] | None = None) -> dict[str, int]:
    """Construct the unique candidate assignment, optionally with forced pivots.

    A negative slack means that this candidate is not a natural-number witness.
    Forced pivots support independent exhaustive checks of the tie-breaking rule.
    """
    validate(rows, alpha, beta)
    n, m = len(rows) - 1, len(rows[0])
    if pivots is None:
        _, pivots, _ = optimal_budget(rows)
    if len(pivots) != n or any(k not in range(m) for k in pivots):
        raise ValueError("Invalid pivot sequence")
    a = {"alpha": alpha, "beta": beta, "alpha_minus_one": alpha - 1,
         "beta_minus_alpha": beta - alpha}
    for s, row in enumerate(rows):
        a[f"v_{s}"] = sum(row)
        for i, x in enumerate(row):
            a[f"u_{s}_{i}"] = x
            a[f"positive_{s}_{i}"] = x - 1
    num, den = alpha, beta
    for s in range(1, n + 1):
        k = pivots[s - 1]
        xs = [rows[s - 1][i] * sum(rows[s]) for i in range(m)]
        ys = [sum(rows[s - 1]) * rows[s][i] for i in range(m)]
        A, B = xs[k], ys[k]
        a[f"A_{s}"], a[f"B_{s}"] = A, B
        for i in range(m):
            a[f"X_{s}_{i}"], a[f"Y_{s}_{i}"] = xs[i], ys[i]
            a[f"e_{s}_{i}"] = int(i == k)
            a[f"slack_{s}_{i}"] = A * ys[i] - B * xs[i] - int(i < k)
        num, den = num * A, den * B
        a[f"C_{s}"], a[f"D_{s}"] = num, den
    a["budget_slack"] = den - num
    return a


def numeric_residuals(a: dict[str, int], n: int, m: int) -> list[int]:
    """Evaluate exactly the full residual list, independently of SymPy."""
    out = []
    for s in range(n + 1):
        for i in range(m):
            out.append(a[f"u_{s}_{i}"] - 1 - a[f"positive_{s}_{i}"])
        out.append(a[f"v_{s}"] - sum(a[f"u_{s}_{i}"] for i in range(m)))
    out += [a["alpha"] - 1 - a["alpha_minus_one"],
            a["beta"] - a["alpha"] - a["beta_minus_alpha"]]
    C, D = a["alpha"], a["beta"]
    for s in range(1, n + 1):
        for i in range(m):
            X, Y, e = a[f"X_{s}_{i}"], a[f"Y_{s}_{i}"], a[f"e_{s}_{i}"]
            out.extend([X - a[f"u_{s-1}_{i}"] * a[f"v_{s}"],
                        Y - a[f"v_{s-1}"] * a[f"u_{s}_{i}"], e*(e-1)])
        es = [a[f"e_{s}_{i}"] for i in range(m)]
        A, B = a[f"A_{s}"], a[f"B_{s}"]
        out.extend([sum(es) - 1,
                    A - sum(es[i] * a[f"X_{s}_{i}"] for i in range(m)),
                    B - sum(es[i] * a[f"Y_{s}_{i}"] for i in range(m))])
        for i in range(m):
            out.append(A*a[f"Y_{s}_{i}"] - B*a[f"X_{s}_{i}"]
                       - a[f"slack_{s}_{i}"] - sum(es[i+1:]))
        out.extend([a[f"C_{s}"] - C*A, a[f"D_{s}"] - D*B])
        C, D = a[f"C_{s}"], a[f"D_{s}"]
    out.append(D - C - a["budget_slack"])
    return out


@dataclass
class PolynomialSystem:
    parameters: list[Any]
    witnesses: list[Any]
    residuals: list[Any]

    @property
    def polynomial(self):
        import sympy as sp
        return sp.Add(*(r*r for r in self.residuals))


def compile_system(n: int, m: int) -> PolynomialSystem:
    """Compile a fixed-horizon quartic sum of squares over natural witnesses."""
    import sympy as sp
    if type(n) is not int or type(m) is not int or n < 0 or m < 2:
        raise ValueError("Require N >= 0 and m >= 2")
    parameters, witnesses, residuals = [], [], []
    def par(name):
        x = sp.Symbol(name, integer=True, nonnegative=True)
        parameters.append(x)
        return x
    def wit(name):
        x = sp.Symbol(name, integer=True, nonnegative=True)
        witnesses.append(x)
        return x
    alpha, beta = par("alpha"), par("beta")
    us = [[par(f"u_{s}_{i}") for i in range(m)] for s in range(n+1)]
    vs = [par(f"v_{s}") for s in range(n+1)]
    for s in range(n+1):
        for i in range(m):
            residuals.append(us[s][i] - 1 - wit(f"positive_{s}_{i}"))
        residuals.append(vs[s] - sum(us[s]))
    residuals += [alpha - 1 - wit("alpha_minus_one"),
                  beta - alpha - wit("beta_minus_alpha")]
    C, D = alpha, beta
    for s in range(1, n+1):
        xs, ys, es = [], [], []
        for i in range(m):
            X, Y, e = wit(f"X_{s}_{i}"), wit(f"Y_{s}_{i}"), wit(f"e_{s}_{i}")
            xs.append(X); ys.append(Y); es.append(e)
            residuals.extend([X-us[s-1][i]*vs[s], Y-vs[s-1]*us[s][i], e*(e-1)])
        A, B = wit(f"A_{s}"), wit(f"B_{s}")
        residuals.extend([sum(es)-1,
                          A-sum(e*x for e,x in zip(es,xs)),
                          B-sum(e*y for e,y in zip(es,ys))])
        for i in range(m):
            residuals.append(A*ys[i]-B*xs[i]-wit(f"slack_{s}_{i}")-sum(es[i+1:]))
        Cnew, Dnew = wit(f"C_{s}"), wit(f"D_{s}")
        residuals.extend([Cnew-C*A, Dnew-D*B])
        C, D = Cnew, Dnew
    residuals.append(D-C-wit("budget_slack"))
    assert len(witnesses) == 5*n*m + m + 4*n + 3
    assert len(residuals) == 5*n*m + m + 6*n + 4
    return PolynomialSystem(parameters, witnesses, residuals)
