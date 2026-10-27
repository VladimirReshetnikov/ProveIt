"""Exact Cauchy mode kernels for a proposed local improvement to tensor contraction.

This is a reusable algebraic prototype, NOT a SAT solver or an implementation
of the full OpenAI tensor-contraction algorithm. It uses standard-library
arithmetic only. No performance claim is inferred from the small examples.

For z even and integer 0 <= j < J, the Newton and skeleton decompositions
of c/(1-z*j) have exactly J rank-one terms. The skeleton valuation bound
requires an additional prime-field congruence when coefficients belong to
an unramified extension; ``check_skeleton_domain`` enforces a sufficient
condition for the included quadratic extension model.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import comb, factorial
from typing import Any


def valuation2_integer(n: int) -> int:
    """Return v_2(n); reject zero, whose valuation is infinite."""
    if n == 0:
        raise ValueError("v_2(0) is infinite")
    n = abs(n)
    return (n & -n).bit_length() - 1


def factorial_valuation2(b: int) -> int:
    if b < 0:
        raise ValueError("b must be nonnegative")
    return b - b.bit_count()


def mode_weight(b: int, family: str = "skeleton") -> int:
    """Uniform lower bound when v_2(c)>=1; b starts at zero."""
    if b < 0:
        raise ValueError("b must be nonnegative")
    extra = {"geometric": 0, "newton": 1, "skeleton": 2}
    if family not in extra:
        raise ValueError("family must be geometric, newton, or skeleton")
    return 1 + b + extra[family] * factorial_valuation2(b)


def kernel_fraction(c: Fraction, z: Fraction, j: int) -> Fraction:
    return Fraction(c) / (1 - Fraction(z) * j)


def source_fraction(j: int, b: int, family: str = "skeleton") -> Fraction:
    if j < 0 or b < 0:
        raise ValueError("j and b must be nonnegative")
    if family == "geometric":
        return Fraction(j**b)
    if family not in ("newton", "skeleton"):
        raise ValueError("unknown family")
    if b > j:
        return Fraction(0)
    result = Fraction(comb(j, b))
    if family == "skeleton":
        result *= 1 - 2 * b * b
        for h in range(b + 1):
            result /= 1 - 2 * h * j
    return result


def target_fraction(c: Fraction, z: Fraction, b: int,
                    family: str = "skeleton") -> Fraction:
    c, z = Fraction(c), Fraction(z)
    if b < 0:
        raise ValueError("b must be nonnegative")
    if family == "geometric":
        return c * z**b
    if family not in ("newton", "skeleton"):
        raise ValueError("unknown family")
    result = c * factorial(b)
    if family == "newton":
        result *= z**b
    else:
        for h in range(b):
            result *= z - 2 * h
    for h in range(b + 1):
        result /= 1 - h * z
    return result


def reconstruct_fraction(c: Fraction, z: Fraction, j: int,
                         tile_length: int, family: str = "skeleton") -> Fraction:
    """Exact finite reconstruction; geometric truncation is not exact over Q."""
    if family not in ("newton", "skeleton"):
        raise ValueError("only Newton and skeleton are finite exact expansions")
    if not 0 <= j < tile_length:
        raise ValueError("j must lie in the tile")
    return sum((target_fraction(c, z, b, family) * source_fraction(j, b, family)
                for b in range(tile_length)), Fraction(0))


@dataclass(frozen=True)
class Mod2Ring:
    """The ring Z/(2**precision), with unit inversion only."""
    precision: int

    def __post_init__(self):
        if self.precision < 1:
            raise ValueError("precision must be positive")

    @property
    def modulus(self): return 1 << self.precision
    @property
    def zero(self): return 0
    @property
    def one(self): return 1
    def integer(self, n): return n % self.modulus
    def add(self, x, y): return (x + y) % self.modulus
    def sub(self, x, y): return (x - y) % self.modulus
    def mul(self, x, y): return (x * y) % self.modulus
    def scale(self, x, n): return (x * n) % self.modulus
    def inv_unit(self, x):
        if not x & 1:
            raise ValueError("attempt to invert a nonunit")
        return pow(x, -1, self.modulus)
    def valuation(self, x):
        x %= self.modulus
        return valuation2_integer(x) if x else self.precision
    def power(self, x, n): return pow(x, n, self.modulus)


@dataclass(frozen=True)
class F4Ring:
    """(Z/2**precision)[U]/(U**2+U+1), represented by (constant, U coefficient).

    Its residue field is F_4. A unit can have any nonzero residue in F_4;
    inversion uses the norm and one ordinary odd-integer inverse.
    """
    precision: int

    def __post_init__(self):
        if self.precision < 1:
            raise ValueError("precision must be positive")

    @property
    def modulus(self): return 1 << self.precision
    @property
    def zero(self): return (0, 0)
    @property
    def one(self): return (1, 0)
    @property
    def generator(self): return (0, 1)
    def integer(self, n): return (n % self.modulus, 0)
    def add(self, x, y):
        return ((x[0] + y[0]) % self.modulus, (x[1] + y[1]) % self.modulus)
    def sub(self, x, y):
        return ((x[0] - y[0]) % self.modulus, (x[1] - y[1]) % self.modulus)
    def mul(self, x, y):
        a, b = x; c, d = y
        return ((a*c - b*d) % self.modulus,
                (a*d + b*c - b*d) % self.modulus)
    def scale(self, x, n):
        return ((x[0] * n) % self.modulus, (x[1] * n) % self.modulus)
    def inv_unit(self, x):
        a, b = x
        norm = (a*a - a*b + b*b) % self.modulus
        if not norm & 1:
            raise ValueError("attempt to invert a nonunit")
        ni = pow(norm, -1, self.modulus)
        return (((a-b)*ni) % self.modulus, (-b*ni) % self.modulus)
    def valuation(self, x):
        return min((valuation2_integer(v % self.modulus) if v % self.modulus
                    else self.precision) for v in x)
    def power(self, x, n):
        if n < 0:
            raise ValueError("nonnegative exponent required")
        result = self.one
        while n:
            if n & 1: result = self.mul(result, x)
            x = self.mul(x, x); n >>= 1
        return result


def ring_div(ring, x, y):
    return ring.mul(x, ring.inv_unit(y))


def kernel_mod(ring, c, z, j: int):
    return ring_div(ring, c, ring.sub(ring.one, ring.scale(z, j)))


def check_skeleton_domain(ring, c, z, tile_length: int) -> None:
    """Check a sufficient domain for the certified skeleton weights.

    All inputs require c and z divisible by 2. In F4 we additionally require
    z/2 congruent to an ordinary scalar modulo 2**ceil(log2 J), which is
    sufficient for all b<J. Actual manuscript row parameters have two extra
    bits of this congruence. At low working precision the condition is read
    modulo that precision, which suffices for the corresponding residues.
    """
    if tile_length < 1:
        raise ValueError("tile_length must be positive")
    if ring.valuation(c) < 1 or ring.valuation(z) < 1:
        raise ValueError("certified weights require c,z divisible by 2")
    if isinstance(ring, F4Ring):
        required = min(ring.precision, (tile_length - 1).bit_length() + 1)
        if z[1] % (1 << required):
            raise ValueError("skeleton weights require prime-field row congruence")


def source_mod(ring, j: int, b: int, family: str = "skeleton"):
    if j < 0 or b < 0:
        raise ValueError("j and b must be nonnegative")
    if family == "geometric":
        return ring.integer(j**b)
    if family not in ("newton", "skeleton"):
        raise ValueError("unknown family")
    if b > j:
        return ring.zero
    result = ring.integer(comb(j, b))
    if family == "skeleton":
        result = ring.scale(result, 1 - 2*b*b)
        denominator = 1
        for h in range(b + 1):
            denominator *= 1 - 2*h*j
        result = ring_div(ring, result, ring.integer(denominator))
    return result


def target_mod(ring, c, z, b: int, family: str = "skeleton"):
    """Evaluate a target exactly modulo 2**p, using no nonunit division."""
    if b < 0:
        raise ValueError("b must be nonnegative")
    if family == "geometric":
        return ring.mul(c, ring.power(z, b))
    if family not in ("newton", "skeleton"):
        raise ValueError("unknown family")
    result = ring.scale(c, factorial(b))
    if family == "newton":
        result = ring.mul(result, ring.power(z, b))
    else:
        for h in range(b):
            result = ring.mul(result, ring.sub(z, ring.integer(2*h)))
    for h in range(b + 1):
        result = ring_div(ring, result, ring.sub(ring.one, ring.scale(z, h)))
    return result


def reconstruct_mod(ring, c, z, j: int, tile_length: int,
                    family: str = "skeleton", truncate: bool = True):
    """Reconstruct the kernel modulo 2**p; truncate by certified weights."""
    if not 0 <= j < tile_length:
        raise ValueError("j must lie in the tile")
    if ring.valuation(c) < 1 or ring.valuation(z) < 1:
        raise ValueError("certified weights require c,z divisible by 2")
    if family == "skeleton":
        check_skeleton_domain(ring, c, z, tile_length)
    if family not in ("geometric", "newton", "skeleton"):
        raise ValueError("unknown family")
    limit = ring.precision if family == "geometric" else tile_length
    result = ring.zero
    for b in range(limit):
        if truncate and mode_weight(b, family) >= ring.precision:
            continue
        term = ring.mul(target_mod(ring, c, z, b, family), source_mod(ring, j, b, family))
        result = ring.add(result, term)
    return result


def actual_deformation_data(ring: F4Ring, a: int, t: int):
    """Return an exact modular W(x,y), and crossing tile (c_x,z_x,J).

    T=t+2**(a+1)*U and S={-2**a,...,2**a-1}. C(T)/C'(0) is
    evaluated by cancelling only known integer powers of two before
    modular arithmetic. Every modular inversion is of an odd unit.
    """
    if a < 1 or t == 0 or not -(1 << a) <= t < (1 << a):
        raise ValueError("invalid grid node")
    i = valuation2_integer(t)
    if i >= a:
        raise ValueError("choose a node of valuation below a")
    L = 1 << a; alpha = 1 << (a + 1)
    grid = range(-L, L)
    odd_derivative = 1
    for q in grid:
        if q:
            value = -q
            odd_derivative *= value // (1 << valuation2_integer(value))
    normalized_product = ring.one
    for q in grid:
        if q == t: continue
        delta = t - q
        v = valuation2_integer(delta)
        factor = ring.add(ring.integer(delta // (1 << v)),
                          ring.scale(ring.generator, alpha >> v))
        normalized_product = ring.mul(normalized_product, factor)
    gamma = ring_div(ring, normalized_product, ring.integer(odd_derivative))

    def W(x: int, y: int):
        if not 0 <= x < L or not 0 <= y < L:
            raise ValueError("ports must lie in packet slots")
        delta = t - y + x
        if delta == 0: return gamma
        v = valuation2_integer(delta)
        unit = ring.add(ring.integer(delta // (1 << v)),
                        ring.scale(ring.generator, alpha >> v))
        numerator = ring.scale(ring.mul(gamma, ring.generator), alpha >> v)
        return ring_div(ring, numerator, unit)

    def crossing(x: int, y0: int):
        if not 0 <= x < L or not 0 <= y0 < (1 << (i + 1)):
            raise ValueError("invalid row or tile")
        if ((x >> i) & 1) != ((y0 >> i) & 1):
            raise ValueError("row and tile are local, not crossing")
        delta = t - y0 + x
        v = valuation2_integer(delta)
        if v > i: raise AssertionError("crossing valuation invariant")
        unit = ring.add(ring.integer(delta // (1 << v)),
                        ring.scale(ring.generator, alpha >> v))
        z = ring.scale(ring.inv_unit(unit), 1 << (i + 1 - v))
        c = W(x, y0)
        J = 1 << (a - i - 1)
        check_skeleton_domain(ring, c, z, J)
        return c, z, J
    return W, crossing


def count_weighted_tuples(precision: int, colors: int, max_modes: int,
                          family: str = "skeleton") -> int:
    """Exact tiny-model count of tuples with weighted degree <precision.

    This is a diagnostic partition DP; its memory depends on precision and
    it is not the polynomial-space enumeration routine of the manuscript.
    """
    if precision < 1 or colors < 0 or max_modes < 0:
        raise ValueError("invalid counting parameters")
    counts = [0] * precision
    counts[0] = 1
    for _ in range(colors):
        for b in range(max_modes):
            w = mode_weight(b, family)
            for total in range(w, precision):
                counts[total] += counts[total - w]
    return sum(counts)


def _main():
    import argparse, json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=80)
    parser.add_argument("--colors", type=int, default=2)
    parser.add_argument("--modes", type=int, default=32)
    args = parser.parse_args()
    result = {
        "scope": "local mode enumeration diagnostic; not a SAT solver",
        "precision": args.precision, "colors": args.colors, "modes_per_color": args.modes,
        "tuple_counts": {f: count_weighted_tuples(args.precision, args.colors, args.modes, f)
                         for f in ("geometric", "newton", "skeleton")},
        "first_weights": {f: [mode_weight(b, f) for b in range(10)]
                          for f in ("geometric", "newton", "skeleton")}}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    _main()
