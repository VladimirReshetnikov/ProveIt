"""Exact five-variable smoothing of finite quadratic Diophantine systems.

Natural zero sets are preserved bijectively; integer zero sets acquire two
sign-related copies. The output is an exact quartic smooth over Spec(Z).
This module produces symbolic certificates, not a Diophantine solver.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import isqrt
from typing import Sequence
import sympy as sp


def exact_int(value: object, name: str = "value") -> int:
    if isinstance(value, bool) or not isinstance(value, (int, sp.Integer)):
        raise TypeError(f"{name} must be an exact integer, not {type(value).__name__}")
    return int(value)


def polynomial_terms(expr: sp.Expr, variables: tuple[sp.Symbol, ...]):
    expr = sp.sympify(expr)
    if expr.has(sp.Float):
        raise TypeError("Floating-point coefficients are not accepted")
    if not expr.free_symbols.issubset(set(variables)):
        raise ValueError("Expression contains undeclared variables")
    if not variables:
        return [((), sp.Integer(exact_int(expr, "constant")))]
    try:
        p = sp.Poly(expr, *variables, domain=sp.ZZ)
    except (sp.PolynomialError, sp.CoercionFailed) as exc:
        raise ValueError("Expected a polynomial with integer coefficients") from exc
    return p.terms()


@dataclass(frozen=True)
class QuadraticSystem:
    variables: tuple[sp.Symbol, ...]
    residuals: tuple[sp.Expr, ...]
    labels: tuple[str, ...] = ()

    def __post_init__(self):
        vv = tuple(self.variables)
        rr = tuple(sp.sympify(f) for f in self.residuals)
        if any(not isinstance(v, sp.Symbol) for v in vv):
            raise TypeError("Variables must be SymPy symbols")
        if len(set(vv)) != len(vv) or len({str(v) for v in vv}) != len(vv):
            raise ValueError("Variables must have distinct names")
        for f in rr:
            if any(sum(alpha) > 2 for alpha, _ in polynomial_terms(f, vv)):
                raise ValueError("Source residual degree exceeds two")
        ll = tuple(self.labels) if self.labels else tuple(f"r{i}" for i in range(len(rr)))
        if len(ll) != len(rr) or len(set(ll)) != len(ll):
            raise ValueError("Residual labels must be distinct and match residuals")
        object.__setattr__(self, "variables", vv)
        object.__setattr__(self, "residuals", rr)
        object.__setattr__(self, "labels", ll)

    def evaluate(self, point: Sequence[object]) -> tuple[sp.Expr, ...]:
        if len(point) != len(self.variables):
            raise ValueError("Point has the wrong dimension")
        values = tuple(sp.sympify(v) for v in point)
        if any(v.has(sp.Float) or v.free_symbols for v in values):
            raise TypeError("Point must contain exact scalar values")
        sub = dict(zip(self.variables, values))
        return tuple(sp.expand(f.subs(sub)) for f in self.residuals)


@dataclass(frozen=True)
class SmoothCertificate:
    source: QuadraticSystem
    t: sp.Symbol
    u: sp.Symbol
    z: tuple[sp.Symbol, ...]
    homogeneous: tuple[sp.Expr, ...]
    H: sp.Expr
    F: sp.Expr

    @property
    def variables(self) -> tuple[sp.Symbol, ...]:
        return self.source.variables + (self.t, self.u) + self.z

    def evaluate(self, point: Sequence[object]) -> sp.Expr:
        if len(point) != len(self.variables):
            raise ValueError("Point has the wrong dimension")
        values = tuple(sp.sympify(v) for v in point)
        if any(v.has(sp.Float) or v.free_symbols for v in values):
            raise TypeError("Point must contain exact scalar values")
        return sp.expand(self.F.subs(dict(zip(self.variables, values))))

    def lift(self, point: Sequence[object], sign: int = 1) -> tuple[int, ...]:
        sign = exact_int(sign, "sign")
        if sign not in (-1, 1):
            raise ValueError("Sign must be +1 or -1")
        aa = tuple(exact_int(a, "source coordinate") for a in point)
        if any(self.source.evaluate(aa)):
            raise ValueError("Source point is not a zero")
        return tuple(sign * a for a in aa) + (sign, sign, 0, 0, 0)

    def jacobian_certificate(self) -> dict[str, sp.Expr]:
        """The actual expanded F and its derivatives are the certificate inputs."""
        E = sum(x * sp.diff(self.F, x) for x in self.source.variables)
        E += self.t * sp.diff(self.F, self.t) - self.u * sp.diff(self.F, self.u)
        D = tuple(sp.diff(self.F, z) for z in self.z)
        J = 8 * self.F - 2 * E - sum((4*z-1)*d for z,d in zip(self.z,D))
        R = self.t * self.u - 1
        four = 4*self.u*(2*R-1)*sp.diff(self.F, self.u) - (2*R+1)*J
        unit = self.z[0] * four - D[0]
        return {"E": sp.expand(E), "J": sp.expand(J),
                "four": sp.expand(four), "unit": sp.expand(unit)}

    def jacobian_coefficients(self) -> tuple[sp.Expr, tuple[sp.Expr, ...]]:
        """Return A,B with A*F + sum(B_i*dF/dv_i) = 1; deg(B_i)<=4."""
        R, z1 = self.t*self.u-1, self.z[0]
        A = -8*z1*(2*R+1)
        B = [2*z1*(2*R+1)*x for x in self.source.variables]
        B += [2*z1*(2*R+1)*self.t, 2*z1*self.u*(2*R-3)]
        B += [z1*(2*R+1)*(4*z-1)-int(j == 0) for j,z in enumerate(self.z)]
        return sp.expand(A), tuple(sp.expand(b) for b in B)

    def export(self) -> dict:
        terms = polynomial_terms(self.F, self.variables)
        return {
            "schema": "smooth-quartic-2", "domain": "integer coefficients",
            "variables": [str(v) for v in self.variables],
            "source_variables": [str(v) for v in self.source.variables],
            "guard_weights": [1,1,2],
            "source_residuals": [str(f) for f in self.source.residuals],
            "source_labels": list(self.source.labels),
            "degree": max(sum(a) for a, _ in terms),
            "monomial_count": len(terms),
            "terms": [{"coefficient": int(c), "exponents": list(a)} for a, c in terms],
        }


def compile_smooth(source: QuadraticSystem, prefix: str = "aux") -> SmoothCertificate:
    if not isinstance(source, QuadraticSystem):
        raise TypeError("Expected a QuadraticSystem")
    if not isinstance(prefix, str) or not prefix.isidentifier():
        raise ValueError("Prefix must be an identifier")
    t, u, *zz = sp.symbols(" ".join(prefix + "_" + s for s in ("t", "u", "z1", "z2", "z3")))
    if {str(v) for v in source.variables} & {str(v) for v in (t, u, *zz)}:
        raise ValueError("Auxiliary variable name collision")
    qq = []
    for f in source.residuals:
        q = sp.Integer(0)
        for alpha, coeff in polynomial_terms(f, source.variables):
            q += coeff * sp.prod(v**a for v, a in zip(source.variables, alpha)) * t**(2-sum(alpha))
        qq.append(sp.expand(q))
    H = sp.expand(sum(q*q for q in qq))
    F = sp.expand(H + (t*u-1)**2 + sum(w*(2*z*z-z) for w,z in zip((1,1,2),zz)))
    return SmoothCertificate(source, t, u, tuple(zz), tuple(qq), H, F)


def four_squares(n: int, search_limit: int = 1_000_000) -> tuple[int, int, int, int]:
    """Deterministic finite pair-table search; intended for moderate examples.

    The mathematical existence theorem has no size cap. This reference routine
    deliberately refuses an allocation beyond its declared search budget.
    """
    n = exact_int(n, "n")
    limit = exact_int(search_limit, "search_limit")
    if n < 0 or limit < 0:
        raise ValueError("n and search_limit must be nonnegative")
    if n > limit:
        raise ValueError("Four-square search budget exceeded; supply a representation")
    pairs = {}
    for a in range(isqrt(n) + 1):
        for b in range(a, isqrt(n - a*a) + 1):
            pairs.setdefault(a*a+b*b, (a, b))
    for s in sorted(pairs):
        if n-s in pairs:
            return pairs[s] + pairs[n-s]
    raise ArithmeticError("Four-square search failed")


def weighted_four_squares(aa: Sequence[int]) -> tuple[int, int, int, int]:
    """Convert four ordinary squares to weights (1,1,2,2) by a parity pair."""
    aa = tuple(exact_int(a) for a in aa)
    if len(aa) != 4 or any(a < 0 for a in aa):
        raise ValueError("Expected four nonnegative integers")
    for i in range(4):
        for j in range(i+1,4):
            if (aa[i]-aa[j]) % 2 == 0:
                other = [aa[k] for k in range(4) if k not in (i,j)]
                return tuple(other) + ((aa[i]+aa[j])//2, abs(aa[i]-aa[j])//2)
    raise ArithmeticError("No equal-parity pair among four integers")


def dyadic_point(cert: SmoothCertificate, representation: Sequence[int] | None = None):
    c = int(sum(v*v for v in cert.source.evaluate((0,)*len(cert.source.variables))))
    K = 1
    while K**4 <= 2*c:
        K *= 2
    N = K**4 - 2*c
    aa = four_squares(N) if representation is None else tuple(exact_int(a) for a in representation)
    if len(aa) != 4 or any(a < 0 for a in aa) or sum(a*a for a in aa) != N:
        raise ValueError("Invalid nonnegative four-square representation")
    A1,A2,A3,B = weighted_four_squares(aa)
    point = (sp.Integer(0),)*len(cert.source.variables)
    point += (sp.Rational(1,K), sp.Rational(K*K+B,K))
    point += tuple(sp.Rational(1,4)+sp.Rational(a,2*K*K) for a in (A1,A2,A3))
    if cert.evaluate(point) != 0:
        raise ArithmeticError("Internal dyadic certificate failure")
    return point, {"c": c, "K": K, "N": N, "four_squares": list(aa),
                   "weighted_representation": [A1,A2,A3,B]}


def two_adic_residues(c: int, precision: int) -> list[dict[str, int]]:
    """Compatible roots of c + 2*z^2 - z mod 2^k, fixing other coordinates."""
    c = exact_int(c, "c")
    precision = exact_int(precision, "precision")
    if precision < 1:
        raise ValueError("Precision must be positive")
    z, modulus = c % 2, 2
    result = [{"modulus": modulus, "z": z}]
    while modulus < 2**precision:
        # derivative 4*z-1 is odd, hence its inverse modulo 2 is one.
        bit = ((c+2*z*z-z)//modulus) % 2
        z += bit*modulus
        modulus *= 2
        if (c+2*z*z-z) % modulus:
            raise ArithmeticError("Internal Hensel failure")
        result.append({"modulus": modulus, "z": z})
    return result
