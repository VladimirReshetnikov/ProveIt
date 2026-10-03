"""Exact, dimension-minimal mixing realizations of rational polynomials.

Compile the joint translation space of one or more polynomials. The transition
matrices are strictly positive, doubly stochastic, commuting and invertible.
Only rational arithmetic is used. See article.tex for theorems and limitations.

Python 3.10+ and SymPy are required. No external services are used.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence
import json
import sympy as sp


def rational(value: object) -> sp.Rational:
    if isinstance(value, (bool, float)) or isinstance(value, sp.Float):
        raise TypeError("Use exact rational numbers, not bool or float")
    if isinstance(value, Fraction):
        return sp.Rational(value.numerator, value.denominator)
    if isinstance(value, (int, sp.Integer, sp.Rational)):
        return sp.Rational(value)
    raise TypeError("Expected int, Fraction, or SymPy Rational")


def natural(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, (int, sp.Integer)):
        raise TypeError("A count must be an exact non-Boolean integer")
    if value < 0:
        raise ValueError("A count must be nonnegative")
    return int(value)


def indices(k: int, d: int) -> tuple[tuple[int, ...], ...]:
    """Multiindices of total degree at most d, in graded lexicographic order."""
    if k < 1 or d < 0:
        raise ValueError("Require at least one variable and nonnegative degree")
    def exact(parts: int, total: int):
        if parts == 1:
            yield (total,)
        else:
            for head in range(total + 1):
                for tail in exact(parts - 1, total - head):
                    yield (head,) + tail
    return tuple(a for total in range(d + 1) for a in exact(k, total))


def polynomial(expr: object, variables: tuple[sp.Symbol, ...]) -> sp.Poly:
    if isinstance(expr, (bool, float, sp.Float)):
        raise TypeError("Polynomial coefficients must be exact rationals")
    e = expr.as_expr() if isinstance(expr, sp.Poly) else sp.sympify(expr)
    if e.has(sp.Float) or e.free_symbols - set(variables):
        raise ValueError("Inexact coefficient or undeclared variable")
    return sp.Poly(e, *variables, domain=sp.QQ)


@dataclass(frozen=True)
class Realization:
    """Immutable output of compile_family; matrices use the row convention.

    This is a mathematical reference implementation, not a large-instance
    optimized solver. A nonzero joint family is required by the compiler.
    """
    variables: tuple[sp.Symbol, ...]
    monomials: tuple[tuple[int, ...], ...]
    basis: tuple[sp.Expr, ...]
    coefficient_matrix: sp.ImmutableMatrix
    pivot_rows: tuple[int, ...]
    pivot_inverse: sp.ImmutableMatrix
    shifts: tuple[sp.ImmutableMatrix, ...]
    E: sp.ImmutableMatrix
    F: sp.ImmutableMatrix
    transitions: tuple[sp.ImmutableMatrix, ...]
    theta: sp.Rational
    q: sp.Rational
    degree: int

    @property
    def rank(self) -> int:
        return len(self.basis)

    @property
    def states(self) -> int:
        return self.rank + 1

    def coordinates(self, expr: object) -> sp.ImmutableMatrix:
        p = polynomial(expr, self.variables)
        v = sp.Matrix([p.coeff_monomial(a) for a in self.monomials])
        # Guard against silently dropping terms above the compiled degree.
        if p.total_degree() > self.degree:
            raise ValueError("Polynomial is outside the compiled module")
        coeff = self.pivot_inverse * v[list(self.pivot_rows), :]
        if self.coefficient_matrix * coeff != v:
            raise ValueError("Polynomial is outside the compiled module")
        return sp.ImmutableMatrix(coeff.T)

    def initial(self, expr: object, epsilon: object | None = None
                ) -> tuple[sp.ImmutableMatrix, sp.Rational]:
        a = self.coordinates(expr)
        w = a * self.E
        height = max(abs(x) for x in w)
        epsilon = (sp.Rational(1, self.states) / (1 + height)
                   if epsilon is None else rational(epsilon))
        if epsilon <= 0:
            raise ValueError("epsilon must be strictly positive")
        u = sp.ones(1, self.states) / self.states
        p = sp.ImmutableMatrix(u + epsilon * w)
        if min(p) <= 0 or sum(p) != 1:
            raise ValueError("The supplied scale does not give a strictly positive distribution")
        return p, epsilon

    def distribution(self, expr: object, counts: Sequence[int],
                     epsilon: object | None = None) -> sp.ImmutableMatrix:
        if len(counts) != len(self.variables):
            raise ValueError("Wrong number of counts")
        p, _ = self.initial(expr, epsilon)
        for M, count in zip(self.transitions, counts):
            p = p * (M ** natural(count))
        return sp.ImmutableMatrix(p)

    def acceptance(self, expr: object, counts: Sequence[int],
                   epsilon: object | None = None) -> sp.Rational:
        return self.distribution(expr, counts, epsilon)[0, 0]

    def recover_polynomial(self, expr: object, epsilon: object | None = None) -> sp.Expr:
        """Recover the centered polynomial from matrices, not from the input.

        Returns g with acceptance(n) = 1/N + q**sum(n) * g(n).
        The result is epsilon * expr. Formula is valid at the empty word too.
        """
        p, _ = self.initial(expr, epsilon)
        N = self.states
        J = sp.ones(N) / N
        H = sp.eye(N) - J
        R = [(M - J) / self.q - H for M in self.transitions]
        row = p - sp.ones(1, N) / N
        out = sp.zeros(N, 1)
        out[0, 0] = 1
        result = sp.Integer(0)
        for alpha in indices(len(self.variables), self.degree):
            term = row
            factor = sp.Integer(1)
            for Ri, ni, ai in zip(R, self.variables, alpha):
                term = term * Ri**ai
                factor *= sp.prod(ni - j for j in range(ai)) / sp.factorial(ai)
            result += (term * out)[0] * factor
        return sp.expand(result)

    def export(self, expr: object, path: str | Path, name: str,
               epsilon: object | None = None) -> None:
        p0, epsilon = self.initial(expr, epsilon)
        pol = polynomial(expr, self.variables)
        def mat(M: sp.MatrixBase) -> list[list[str]]:
            return [[str(M[i,j]) for j in range(M.cols)] for i in range(M.rows)]
        payload = {
            "format": "mixing-polynomial-realization-v1",
            "name": name, "variables": [str(v) for v in self.variables],
            "degree": self.degree, "translation_rank": self.rank,
            "states": self.states, "theta": str(self.theta), "q": str(self.q),
            "epsilon": str(epsilon), "equilibrium_acceptance": f"1/{self.states}",
            "polynomial_terms": [{"exponents": list(a), "coefficient": str(c)}
                                 for a,c in pol.terms()],
            "basis": [str(b) for b in self.basis],
            "initial": [str(x) for x in p0],
            "transitions": [mat(M) for M in self.transitions],
            "shifts": [mat(A) for A in self.shifts],
            "E": mat(self.E), "F": mat(self.F),
            "domain": "nonnegative integer letter counts, including all zero",
        }
        Path(path).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def compile_family(expressions: Iterable[object], variables: Sequence[sp.Symbol],
                   theta: object = Fraction(1, 2)) -> Realization:
    """Compile one common minimal module for the supplied nonzero family.

    Each family member, and every polynomial in its translation span, can be
    loaded using model.initial(expr). The same transitions and accepting state
    are retained for every such input.
    """
    vs = tuple(variables)
    if not vs or any(not isinstance(v, sp.Symbol) for v in vs) or len(set(vs)) != len(vs):
        raise ValueError("Supply a nonempty tuple of distinct SymPy symbols")
    th = rational(theta)
    if not 0 < th < 1:
        raise ValueError("theta must satisfy 0 < theta < 1")
    ps = tuple(polynomial(e, vs) for e in expressions)
    if not ps or all(p.is_zero for p in ps):
        raise ValueError("The joint polynomial family must be nonzero")
    d = max(int(p.total_degree()) for p in ps if not p.is_zero)
    monos = indices(len(vs), d)
    candidates = []
    for p in ps:
        for alpha in monos:
            f = p.as_expr()
            for v, a in zip(vs, alpha):
                if a:
                    f = sp.diff(f, v, a)
            if f != 0:
                candidates.append(sp.expand(f))
    def vector(f: sp.Expr) -> sp.Matrix:
        pp = sp.Poly(f, *vs, domain=sp.QQ)
        return sp.Matrix([pp.coeff_monomial(a) for a in monos])
    all_vectors = sp.Matrix.hstack(*(vector(f) for f in candidates))
    independent = all_vectors.rref()[1]
    basis = tuple(candidates[j] for j in independent)
    B = sp.Matrix.hstack(*(vector(f) for f in basis))
    pivots = tuple(B.T.rref()[1])
    pivot_inv = B[list(pivots), :].inv()
    shifts = []
    for v in vs:
        S = sp.Matrix.hstack(*(vector(sp.expand(f.subs(v, v + 1))) for f in basis))
        T = pivot_inv * S[list(pivots), :]
        if B*T != S:
            raise ArithmeticError("Translation closure failed")
        shifts.append(sp.ImmutableMatrix(T.T))
    r = len(basis)
    zero = {v: 0 for v in vs}
    b = sp.Matrix([f.subs(zero) for f in basis])
    if b.is_zero_matrix:
        raise ArithmeticError("Nonzero translation module has zero evaluation functional")
    # Complete b to an invertible rational matrix C with first column b.
    columns = [b]
    for j in range(r):
        e = sp.eye(r)[:,j]
        if sp.Matrix.hstack(*columns, e).rank() > len(columns):
            columns.append(e)
        if len(columns) == r:
            break
    C = sp.Matrix.hstack(*columns)
    E = C.row_join(-C*sp.ones(r,1))
    F = E.T*(E*E.T).inv()
    N = r+1
    J = sp.ones(N)/N
    centered = [F*A*E for A in shifts]
    K = max(abs(x) for M in centered for x in M)
    q = th/(1+N*K)
    matrices = tuple(sp.ImmutableMatrix(J + q*M) for M in centered)
    if E*F != sp.eye(r) or F*E != sp.eye(N)-J:
        raise ArithmeticError("Mass/information embedding identities failed")
    for M in matrices:
        if min(M) <= 0 or M*sp.ones(N,1) != sp.ones(N,1) or sp.ones(1,N)*M != sp.ones(1,N):
            raise ArithmeticError("Stochastic invariant failed")
        if any(abs(x-sp.Rational(1,N)) >= th/N for x in M):
            raise ArithmeticError("Mixing margin failed")
    for M in matrices:
        for L in matrices:
            if M*L != L*M:
                raise ArithmeticError("Commutation failed")
    return Realization(vs, monos, basis, sp.ImmutableMatrix(B), pivots,
                       sp.ImmutableMatrix(pivot_inv), tuple(shifts),
                       sp.ImmutableMatrix(E), sp.ImmutableMatrix(F), matrices,
                       th, q, d)


def separation_horizon(theta: object, delta: object) -> int:
    """Return least L with theta**L < delta, using exact rational comparisons."""
    th, de = rational(theta), rational(delta)
    if not 0 < th < 1 or de <= 0:
        raise ValueError("Require 0 < theta < 1 and delta > 0")
    L, power = 0, sp.Integer(1)
    while power >= de:
        power *= th
        L += 1
    return L
