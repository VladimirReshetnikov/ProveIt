#!/usr/bin/env python3
"""Richardson reduction examples and exact rational interval certificates.

Standard-library-only demonstration. This implements the explicit analytic
compiler for a supplied natural-variable polynomial; it does not implement
MRDP or an identity decision procedure. All bounds used for certificates are
fractions. No floating-point arithmetic is used.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction as Q
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Expr:
    op: str
    args: tuple["Expr", ...] = ()
    value: Q | None = None


def rat(value: int | Q) -> Expr:
    return Expr("rat", value=Q(value))


T = Expr("var")
PI = Expr("pi")


def add(a: Expr, b: Expr) -> Expr:
    if a.op == "rat" and a.value == 0:
        return b
    if b.op == "rat" and b.value == 0:
        return a
    if a.op == b.op == "rat":
        return rat(a.value + b.value)  # type: ignore[operator]
    return Expr("add", (a, b))


def mul(a: Expr, b: Expr) -> Expr:
    if a.op == "rat":
        if a.value == 0:
            return a
        if a.value == 1:
            return b
    if b.op == "rat":
        if b.value == 0:
            return b
        if b.value == 1:
            return a
    if a.op == b.op == "rat":
        return rat(a.value * b.value)  # type: ignore[operator]
    return Expr("mul", (a, b))


def neg(a: Expr) -> Expr:
    return mul(rat(-1), a)


def power(a: Expr, n: int) -> Expr:
    if n < 0:
        raise ValueError("Only nonnegative integer powers are allowed")
    result = rat(1)
    base = a
    # The repeated-squaring loop is bounded by the supplied exponent.
    for _ in range(n.bit_length()):
        if n & 1:
            result = mul(result, base)
        n >>= 1
        if n:
            base = mul(base, base)
    return result


def sin(a: Expr) -> Expr:
    return Expr("sin", (a,))


def absolute(a: Expr) -> Expr:
    return Expr("abs", (a,))


def sum_expr(items: list[Expr]) -> Expr:
    result = rat(0)
    for item in items:
        result = add(result, item)
    return result


@dataclass(frozen=True)
class Polynomial:
    variables: int
    terms: tuple[tuple[int, tuple[int, ...]], ...]
    name: str = "polynomial"

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> "Polynomial":
        n = data["variables"]
        if type(n) is not int or n < 1:
            raise ValueError("variables must be a positive integer")
        combined: dict[tuple[int, ...], int] = {}
        for term in data["terms"]:
            c, exps = term["coeff"], tuple(term["powers"])
            if type(c) is not int:
                raise ValueError("Coefficients must be integers")
            if len(exps) != n or any(type(k) is not int or k < 0 for k in exps):
                raise ValueError("Each powers vector needs n nonnegative integers")
            combined[exps] = combined.get(exps, 0) + c
        terms = tuple((c, exps) for exps, c in sorted(combined.items()) if c)
        return cls(n, terms, str(data.get("name", "polynomial")))

    @property
    def coefficient_bound(self) -> int:
        return max(1, sum(abs(c) for c, _ in self.terms))

    @property
    def degree_bound(self) -> int:
        return max(1, max((sum(exps) for _, exps in self.terms), default=0))

    def at(self, args: list[Expr]) -> Expr:
        if len(args) != self.variables:
            raise ValueError("Incorrect number of arguments")
        monomials = []
        for c, exps in self.terms:
            term = rat(c)
            for a, k in zip(args, exps):
                term = mul(term, power(a, k))
            monomials.append(term)
        return sum_expr(monomials)


@dataclass(frozen=True)
class Reduction:
    polynomial: Polynomial
    h: tuple[Expr, ...]
    u: tuple[Expr, ...]
    radius: Expr
    lipschitz_bound: Expr
    gap: Expr
    identity: Expr


def compile_reduction(p: Polynomial) -> Reduction:
    """Compile E(t)=|F(u(t))|-F(u(t)), with u_j=(t sin(t^(2j-1)))^2."""
    h = tuple(mul(T, sin(power(T, 2 * j - 1))) for j in range(1, p.variables + 1))
    u = tuple(power(a, 2) for a in h)
    radius = add(rat(1), sum_expr([power(a, 2) for a in u]))
    cb, db = p.coefficient_bound, p.degree_bound
    lip = mul(rat(cb * db), power(mul(rat(2), radius), db))
    pp = p.at(list(u))
    penalty = sum_expr([power(sin(mul(PI, a)), 2) for a in u])
    energy = add(power(pp, 2), mul(power(lip, 2), penalty))
    gap = add(mul(rat(4), energy), rat(-1))
    identity = add(absolute(gap), neg(gap))
    return Reduction(p, h, u, radius, lip, gap, identity)


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("Reversed interval")

    @staticmethod
    def point(q: int | Q) -> "Interval":
        return Interval(Q(q), Q(q))

    @property
    def width(self) -> Q:
        return self.hi - self.lo

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __mul__(self, other: "Interval") -> "Interval":
        corners = [self.lo * other.lo, self.lo * other.hi,
                   self.hi * other.lo, self.hi * other.hi]
        return Interval(min(corners), max(corners))

    def abs(self) -> "Interval":
        if self.lo >= 0:
            return self
        if self.hi <= 0:
            return -self
        return Interval(Q(0), max(-self.lo, self.hi))

    def negative_part_twice(self) -> "Interval":
        """Exact image interval for v -> |v|-v, preserving dependence."""
        return Interval(max(Q(0), -2 * self.hi), max(Q(0), -2 * self.lo))

    def dyadic_outer(self, bits: int) -> "Interval":
        scale = 1 << bits
        low = (self.lo.numerator * scale) // self.lo.denominator
        high = -((-self.hi.numerator * scale) // self.hi.denominator)
        return Interval(Q(low, scale), Q(high, scale))

    def contains(self, q: int | Q) -> bool:
        return self.lo <= q <= self.hi

    def as_json(self) -> dict[str, Any]:
        return {
            "lo": str(self.lo), "hi": str(self.hi),
            "width": str(self.width),
            "outward_decimal_display": [decimal_outer(self.lo, False),
                                         decimal_outer(self.hi, True)],
        }


def decimal_outer(q: Q, upper: bool, digits: int = 24) -> str:
    # Human-readable display only; certificate checks use the exact fractions.
    with localcontext() as ctx:
        ctx.prec = digits
        ctx.rounding = ROUND_CEILING if upper else ROUND_FLOOR
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def atan_reciprocal(k: int, bits: int) -> Interval:
    """Alternating-series enclosure for atan(1/k), k>=2."""
    if k < 2:
        raise ValueError("k must be at least 2")
    eps = Q(1, 1 << bits)
    partial, power_k = Q(0), k
    for j in range(bits + 4):
        term = Q(1, (2 * j + 1) * power_k)
        partial += term if j % 2 == 0 else -term
        power_k *= k * k
        following = Q(1, (2 * j + 3) * power_k)
        if following <= eps:
            if j % 2 == 0:
                return Interval(partial - following, partial)
            return Interval(partial, partial + following)
    raise AssertionError("Proved alternating-series bound was not reached")


def pi_interval(bits: int) -> Interval:
    # Machin's identity: pi = 16 atan(1/5) - 4 atan(1/239).
    a = atan_reciprocal(5, bits + 6)
    b = atan_reciprocal(239, bits + 6)
    return (Interval.point(16) * a + Interval.point(-4) * b).dyadic_outer(bits)


def sine_point(q: Q, bits: int) -> Interval:
    """Power-series enclosure with a geometric absolute-tail certificate.

    With M terms already summed, the first omitted term has absolute value
    a=|q|^(2M+1)/(2M+1)!. If the ratio of successive omitted absolute terms
    is at most 1/2, the entire tail is at most 2a. The for-loop has an
    explicit primitive recursive bound; it never uses unbounded search.
    """
    if q == 0:
        return Interval.point(0)
    eps = Q(1, 1 << (bits + 3))
    aq = abs(q)
    r = (aq.numerator + aq.denominator - 1) // aq.denominator
    r = max(1, r)
    limit = r * r + r + bits + 8
    partial, term = Q(0), q
    for j in range(limit):
        ratio = q * q / ((2 * j + 2) * (2 * j + 3))
        error = 2 * abs(term)
        if ratio <= Q(1, 2) and error <= eps:
            return Interval(partial - error, partial + error)
        partial += term
        term = -term * ratio
    raise AssertionError("Proved sine-tail bound was not reached")


def sine_interval(a: Interval, bits: int) -> Interval:
    midpoint = (a.lo + a.hi) / 2
    radius = a.width / 2
    if radius >= 1:
        return Interval(Q(-1), Q(1))
    center = sine_point(midpoint, bits)
    # Global one-Lipschitz bound for sine, then its range bound.
    lo = max(Q(-1), center.lo - radius)
    hi = min(Q(1), center.hi + radius)
    return Interval(lo, hi).dyadic_outer(bits)


class Evaluator:
    def __init__(self, q: Q, work_bits: int):
        if work_bits < 0:
            raise ValueError("Precision must be nonnegative")
        self.q = q
        self.bits = work_bits
        # Retain every key node: Python may recycle id(e) after an ephemeral
        # expression is collected. A bare id -> interval cache is unsound
        # when callers reuse this evaluator for newly constructed roots.
        self.cache: dict[int, tuple[Expr, Interval]] = {}
        self.pi: Interval | None = None

    def evaluate(self, e: Expr) -> Interval:
        cached = self.cache.get(id(e))
        if cached is not None:
            cached_expr, cached_interval = cached
            if cached_expr is not e:
                raise AssertionError("Expression identity collision in retained cache")
            return cached_interval
        if e.op == "var":
            result = Interval.point(self.q)
        elif e.op == "rat":
            assert e.value is not None
            result = Interval.point(e.value)
        elif e.op == "pi":
            if self.pi is None:
                self.pi = pi_interval(self.bits)
            result = self.pi
        elif e.op == "add":
            result = self.evaluate(e.args[0]) + self.evaluate(e.args[1])
        elif e.op == "mul":
            result = self.evaluate(e.args[0]) * self.evaluate(e.args[1])
        elif e.op == "sin":
            result = sine_interval(self.evaluate(e.args[0]), self.bits)
        elif e.op == "abs":
            result = self.evaluate(e.args[0]).abs()
        else:
            raise ValueError(f"Unsupported node: {e.op}")
        result = result.dyadic_outer(self.bits)
        self.cache[id(e)] = (e, result)
        return result


def magnitude_and_width(e: Expr, q: Q) -> tuple[int, int]:
    """A priori magnitude B and width-amplification W for common precision.

    If delta=2^-work_bits and W_root*delta<=1, every interval has width at
    most W_node*delta. Endpoint magnitudes are then <=B_node+1. See README.
    """
    cache: dict[int, tuple[int, int]] = {}

    def walk(v: Expr) -> tuple[int, int]:
        if id(v) in cache:
            return cache[id(v)]
        if v.op in ("rat", "var"):
            a = abs(q if v.op == "var" else v.value)
            b = (a.numerator + a.denominator - 1) // a.denominator + 1
            result = (b, 1)
        elif v.op == "pi":
            result = (4, 3)
        else:
            b1, w1 = walk(v.args[0])
            if v.op in ("add", "mul"):
                b2, w2 = walk(v.args[1])
                if v.op == "add":
                    result = (b1 + b2, 2 + w1 + w2)
                else:
                    result = (b1 * b2, 2 + (b1 + 1) * w2 + (b2 + 1) * w1)
            elif v.op == "sin":
                result = (1, w1 + 3)
            elif v.op == "abs":
                result = (b1, w1 + 2)
            else:
                raise ValueError(v.op)
        cache[id(v)] = result
        return result

    return walk(e)


def certified_evaluate(e: Expr, q: Q, target_bits: int) -> tuple[Interval, int]:
    if target_bits < 0:
        raise ValueError("Precision must be nonnegative")
    _, w = magnitude_and_width(e, q)
    work_bits = target_bits + w.bit_length() + 2
    interval = Evaluator(q, work_bits).evaluate(e)
    if interval.width > Q(1, 1 << target_bits):
        raise AssertionError("A priori precision bound failed")
    return interval, work_bits


def expression_dag(e: Expr) -> dict[str, Any]:
    nodes: list[dict[str, Any]] = []
    indices: dict[int, int] = {}

    def visit(v: Expr) -> int:
        if id(v) in indices:
            return indices[id(v)]
        args = [visit(a) for a in v.args]
        item: dict[str, Any] = {"op": v.op}
        if args:
            item["args"] = args
        if v.op == "rat":
            item["value"] = str(v.value)
        index = len(nodes)
        nodes.append(item)
        indices[id(v)] = index
        return index

    root = visit(e)
    return {"format": "richardson-expression-dag-v1", "nodes": nodes, "root": root,
            "note": "Sharing is an encoding convenience; unfold to obtain a legal expression tree."}


def reduction_certificate(p: Polynomial, q: Q, bits: int) -> dict[str, Any]:
    reduction = compile_reduction(p)
    generic, work = certified_evaluate(reduction.identity, q, bits)
    ev = Evaluator(q, work)
    gap = ev.evaluate(reduction.gap)
    tight = gap.negative_part_twice()
    if tight.lo < generic.lo or tight.hi > generic.hi:
        raise AssertionError("Dependent final simplification escaped generic interval")
    return {
        "polynomial": p.name,
        "input_rational": str(q),
        "target_bits": bits,
        "work_bits": work,
        "C": p.coefficient_bound,
        "D": p.degree_bound,
        "gap_interval": gap.as_json(),
        "generic_identity_interval": generic.as_json(),
        "identity_interval": tight.as_json(),
        "certified_nonzero_at_this_input": tight.lo > 0 or tight.hi < 0,
        "scope": "A finite rational enclosure at one rational input, not a global identity test.",
    }


def load_poly(path: Path) -> Polynomial:
    return Polynomial.from_json(json.loads(path.read_text(encoding="utf-8")))


def demo(bits: int) -> dict[str, Any]:
    base = Path(__file__).resolve().parent / "examples"
    samples = [
        ("linear_root.json", Q("1.11415714087193")),
        ("linear_no_natural_root.json", Q("1.11415714087193")),
        ("quadratic_no_root.json", Q("1.11415714087193")),
        ("zero_polynomial.json", Q(0)),
    ]
    certificates = [reduction_certificate(load_poly(base / name), q, bits)
                    for name, q in samples]
    return {"method": "Exact Fraction interval arithmetic with bounded series truncation",
            "universal_MRDP_compiler_implemented": False,
            "certificates": certificates}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p_demo = sub.add_parser("demo")
    p_demo.add_argument("--bits", type=int, default=48)
    p_demo.add_argument("--output", type=Path)
    p_eval = sub.add_parser("evaluate")
    p_eval.add_argument("polynomial", type=Path)
    p_eval.add_argument("--x", required=True, help="Exact fraction or finite decimal")
    p_eval.add_argument("--bits", type=int, default=48)
    p_eval.add_argument("--output", type=Path)
    p_compile = sub.add_parser("compile")
    p_compile.add_argument("polynomial", type=Path)
    p_compile.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.command == "demo":
        result = demo(args.bits)
    elif args.command == "evaluate":
        result = reduction_certificate(load_poly(args.polynomial), Q(args.x), args.bits)
    else:
        p = load_poly(args.polynomial)
        result = {"polynomial": p.name, "C": p.coefficient_bound, "D": p.degree_bound,
                  "expression": expression_dag(compile_reduction(p).identity)}
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
        print(f"Wrote {args.output}")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
