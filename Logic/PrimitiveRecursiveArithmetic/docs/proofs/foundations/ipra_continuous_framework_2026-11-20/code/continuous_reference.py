"""Exact rational reference implementations for the accompanying report.

The calculations here are demonstrations, not object-language iPRA proofs.
All loops have explicit finite lengths.  Python Fraction is a convenient
realization of the report's positive-denominator rational arithmetic.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from typing import Callable


def dyadic(k: int) -> F:
    if k < 0:
        raise ValueError("negative precision")
    return F(1, 1 << k)


def ceil_fraction(x: F) -> int:
    return -((-x.numerator) // x.denominator)


def precision_for(u: F) -> int:
    """Least m with 2**m >= max(1,u), by the report's bounded search."""
    if u < 0:
        raise ValueError("negative majorant")
    target = max(F(1), u)
    for m in range(ceil_fraction(target) + 2):
        if F(1 << m) >= target:
            return m
    raise AssertionError("the elementary bound 2**m >= m+1 was violated")


def round_down(x: F, p: int) -> F:
    scale = 1 << p
    return F((x.numerator * scale) // x.denominator, scale)


@dataclass(frozen=True)
class Formula:
    """A fixed continuous formula with exact rational atomic evaluation.

    W is a Lipschitz bound for the sup metric on its free variables.
    C bounds the finite-net error by C/2**k.  Additive coefficient rules
    specialize the report's general connective rule and are sometimes sharper.
    """
    op: str
    args: tuple = ()

    def weights(self) -> tuple[F, F]:
        if self.op == "const":
            return F(0), F(0)
        if self.op == "var":
            return F(1), F(0)
        if self.op == "scale":
            a, f = self.args
            w, c = f.weights()
            return abs(a) * w, abs(a) * c
        if self.op == "abs":
            return self.args[0].weights()
        if self.op == "add":
            a, b = (f.weights() for f in self.args)
            return a[0] + b[0], a[1] + b[1]
        if self.op in ("min", "max"):
            w = [f.weights() for f in self.args]
            return max(a for a, _ in w), max(b for _, b in w)
        if self.op in ("inf", "sup"):
            _, f = self.args
            w, c = f.weights()
            return w, c + w
        raise ValueError(self.op)

    def evaluate(self, k: int, env: dict[str, F] | None = None) -> F:
        env = {} if env is None else env
        if self.op == "const":
            return F(self.args[0])
        if self.op == "var":
            return env[self.args[0]]
        if self.op == "scale":
            return self.args[0] * self.args[1].evaluate(k, env)
        if self.op == "abs":
            return abs(self.args[0].evaluate(k, env))
        if self.op == "add":
            return sum((f.evaluate(k, env) for f in self.args), F(0))
        if self.op in ("min", "max"):
            fn = min if self.op == "min" else max
            return fn(f.evaluate(k, env) for f in self.args)
        if self.op in ("inf", "sup"):
            name, body = self.args
            count = 1 << k
            values = (body.evaluate(k, {**env, name: F(j, count)})
                      for j in range(count + 1))
            return min(values) if self.op == "inf" else max(values)
        raise ValueError(self.op)


def radius_problem() -> Formula:
    # inf_x sup_y |x-y| on [0,1], whose exact value is 1/2.
    diff = Formula("add", (Formula("var", ("x",)),
                            Formula("scale", (F(-1), Formula("var", ("y",))))))
    return Formula("inf", ("x", Formula("sup", ("y", Formula("abs", (diff,))))))


def asymmetric_problem() -> Formula:
    # inf_x max(x,(1-x)/2), uniquely minimized at x=1/3, value 1/3.
    x = Formula("var", ("x",))
    rhs = Formula("add", (Formula("const", (F(1, 2),)),
                           Formula("scale", (F(-1, 2), x))))
    return Formula("inf", ("x", Formula("max", (x, rhs))))


@dataclass(frozen=True)
class EulerPolygon:
    T: F
    p: int
    nodes: tuple[F, ...]

    @property
    def N(self) -> int:
        return len(self.nodes) - 1

    def value(self, t: F) -> F:
        if not (0 <= t <= self.T):
            raise ValueError("query outside proved tube")
        if t == self.T:
            return self.nodes[-1]
        u = t * self.N / self.T
        j = u.numerator // u.denominator
        return self.nodes[j] + (u - j) * (self.nodes[j + 1] - self.nodes[j])


def euler_table(evaluator: Callable[[F, F, int], F], x0: F,
                T: F, N: int, p: int) -> EulerPolygon:
    if N < 1 or T <= 0:
        raise ValueError("invalid mesh")
    h = T / N
    out = [x0]
    for j in range(N):
        slope = evaluator(j * h, out[-1], p)
        out.append(out[-1] + h * slope)
    return EulerPolygon(T, p, tuple(out))


def example_ode(n: int) -> tuple[EulerPolygon, F]:
    # F(t,x)=x, but the evaluator genuinely rounds to the requested precision.
    T, M, Lx, Lt = F(1, 4), F(2), F(1), F(0)
    B = M + 1
    K = Lt + Lx * B
    G = F(3 ** ceil_fraction(Lx * T))
    C = G * T * (1 + K * T)
    c = precision_for(8 * max(F(1), C))
    p = n + c
    N = 1 << p
    poly = euler_table(lambda t, x, p: round_down(x, p), F(1), T, N, p)
    return poly, C * dyadic(p)


def exp_enclosure(x: F, terms: int = 24) -> tuple[F, F]:
    """Independent positive Taylor enclosure; valid for 0<=x<=1, terms>=1."""
    if not (0 <= x <= 1 and terms >= 1):
        raise ValueError("unsupported exponential enclosure")
    term, total = F(1), F(0)
    for j in range(terms):
        total += term
        term *= x / (j + 1)
    # The remaining ratios are <= 1/2, hence the tail is <= 2*term.
    return total, total + 2 * term


@dataclass(frozen=True)
class CQ:
    re: F = F(0)
    im: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "re", F(self.re))
        object.__setattr__(self, "im", F(self.im))

    def __add__(self, other: CQ) -> CQ:
        return CQ(self.re + other.re, self.im + other.im)

    def __neg__(self) -> CQ:
        return CQ(-self.re, -self.im)

    def __sub__(self, other: CQ) -> CQ:
        return self + (-other)

    def __mul__(self, other: CQ) -> CQ:
        return CQ(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    def scale(self, scalar: F) -> CQ:
        return CQ(self.re * scalar, self.im * scalar)

    def norm2(self) -> F:
        return self.re * self.re + self.im * self.im

    def inverse(self) -> CQ:
        q = self.norm2()
        if q == 0:
            raise ZeroDivisionError("unguarded reciprocal")
        return CQ(self.re / q, -self.im / q)

    def __truediv__(self, other: CQ) -> CQ:
        return self * other.inverse()

    def __pow__(self, n: int) -> CQ:
        if n < 0:
            return self.inverse() ** (-n)
        value = CQ(1)
        for _ in range(n):
            value = value * self
        return value


UNIT_SQUARE = (CQ(-1, -1), CQ(1, -1), CQ(1, 1), CQ(-1, 1), CQ(-1, -1))


def segment_distance2(a: CQ, b: CQ, w: CQ) -> F:
    v, u = b - a, a - w
    vv = v.norm2()
    if vv == 0:
        return u.norm2()
    lam = -(u.re * v.re + u.im * v.im) / vv
    lam = min(F(1), max(F(0), lam))
    return (u + v.scale(lam)).norm2()


def clearance(poly: tuple[CQ, ...], w: CQ, delta: F) -> bool:
    return (delta > 0 and len(poly) >= 2 and poly[0] == poly[-1]
            and all(segment_distance2(a, b, w) >= delta * delta
                    for a, b in zip(poly, poly[1:])))


def length_upper(poly: tuple[CQ, ...]) -> F:
    return sum((abs((b-a).re) + abs((b-a).im)
                for a, b in zip(poly, poly[1:])), F(0))


def cauchy_sum(poly: tuple[CQ, ...], w: CQ, delta: F, N: int,
               datum: Callable[[CQ], CQ] = lambda z: CQ(1),
               coefficient: int = 0) -> CQ:
    if N < 1 or coefficient < 0 or not clearance(poly, w, delta):
        raise ValueError("positive-clearance guard failed")
    total = CQ()
    for a, b in zip(poly, poly[1:]):
        v = b - a
        for j in range(N):
            z = a + v.scale(F(j, N))
            total += (datum(z) / ((z - w) ** (coefficient + 1)) * v).scale(F(1, N))
    return total


def atan_enclosure(x: F, terms: int = 24) -> tuple[F, F]:
    """Alternating geometric-integral enclosure for 0<=x<=1/2."""
    if not (0 <= x <= F(1, 2)) or terms < 1:
        raise ValueError("unsupported arctangent enclosure")
    total = sum(((-1) ** j * x ** (2 * j + 1) / (2 * j + 1)
                 for j in range(terms)), F(0))
    adjacent = total + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
    return min(total, adjacent), max(total, adjacent)


def square_integral_enclosure() -> tuple[F, F]:
    # The square integral of dz/z is 8 i atan(1).
    # atan(1)=atan(1/2)+atan(1/3), by the elementary tangent addition identity.
    a, b = atan_enclosure(F(1, 2)), atan_enclosure(F(1, 3))
    return 8 * (a[0] + b[0]), 8 * (a[1] + b[1])
