#!/usr/bin/env python3
"""Exact arithmetic companions for the constructive Mordell--Weil report.

Only the Python standard library is used. Points are None (the identity O)
or pairs of Fraction objects. Heights are the multiplicative x-height,
with H(O)=1, and its integer binary logarithm h=ceil(log2 H).

These routines do not discover or certify a complete set of representatives
modulo 2E(Q). In particular, a successful finite test does not establish a
universal covering assertion. bounded_division_search has a proved finite
search shape, but completeness requires the representative-cover hypothesis
and the report's height theorem.

Python API errors raise ValueError/TypeError. The iPRA implementation instead
totalizes invalid inputs with a failure tag and default output. isqrt,
bit_length, gcd, and binary scalar multiplication can be replaced by bounded
scans/recursions; no unbounded witness search is part of the mathematical
algorithms here. There is no universal interpreter for arbitrary PR programs.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt
from typing import Iterator, Optional, Sequence

Point = Optional[tuple[Fraction, Fraction]]


def ceil_log2(n: int) -> int:
    """Least k with n <= 2**k, for a positive integer n."""
    if not isinstance(n, int):
        raise TypeError("ceil_log2 requires an integer")
    if n < 1:
        raise ValueError("ceil_log2 requires a positive integer")
    return (n - 1).bit_length()


def x_height(p: Point) -> int:
    if p is None:
        return 1
    x = Fraction(p[0])
    return max(abs(x.numerator), x.denominator)


def integer_height(p: Point) -> int:
    return ceil_log2(x_height(p))


def point_text(p: Point) -> str:
    if p is None:
        return "O"
    return "(" + str(p[0]) + ", " + str(p[1]) + ")"


def poly_mul(a: Sequence[int], b: Sequence[int]) -> list[int]:
    """Homogeneous binary coefficient convolution, descending X degrees."""
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i + j] += u * v
    return out


def poly_add(a: Sequence[int], b: Sequence[int]) -> list[int]:
    if len(a) != len(b):
        raise ValueError("coefficient lists must have the same degree")
    return [u + v for u, v in zip(a, b)]


def homogeneous_eval(coefficients: Sequence[int], x: int, z: int) -> int:
    if not coefficients:
        raise ValueError("a homogeneous form needs a coefficient list")
    d = len(coefficients) - 1
    return sum(c * x ** (d - i) * z ** i
               for i, c in enumerate(coefficients))


def positive_divisors(n: int) -> list[int]:
    """Complete sorted positive divisor list for n>0, with explicit finite fuel."""
    if n <= 0:
        raise ValueError("positive_divisors requires n>0")
    small, large = [], []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
    return small + list(reversed(large))


def rational_roots(coefficients: Sequence[int]) -> list[Fraction]:
    """All rational roots of a nonzero integer polynomial, constant term first.

    Remove powers of X, recording the root zero. If the first remaining
    coefficient is c and the leading coefficient is a, every nonzero
    reduced root m/n has |m| dividing |c| and n dividing |a|. The resulting
    finite rational-root search is unconditional and primitive recursive.
    """
    cs = list(coefficients)
    while cs and cs[-1] == 0:
        cs.pop()
    if not cs:
        raise ValueError("the zero polynomial has infinitely many rational roots")
    roots = set()
    while cs[0] == 0:
        roots.add(Fraction(0))
        cs.pop(0)
    if len(cs) == 1:
        return sorted(roots)
    numerators = positive_divisors(abs(cs[0]))
    denominators = positive_divisors(abs(cs[-1]))
    for n in denominators:
        for m in numerators:
            if gcd(m, n) != 1:
                continue
            for sign in (-1, 1):
                x = Fraction(sign * m, n)
                value = Fraction(0)
                for c in reversed(cs):
                    value = value * x + c
                if value == 0:
                    roots.add(x)
    return sorted(roots)


def rational_square_roots(q: Fraction) -> list[Fraction]:
    """The complete (possibly empty) list of rational square roots."""
    q = Fraction(q)
    if q < 0:
        return []
    u, v = isqrt(q.numerator), isqrt(q.denominator)
    if u * u != q.numerator or v * v != q.denominator:
        return []
    r = Fraction(u, v)
    return [r] if r == 0 else [-r, r]


def determinant(matrix: Sequence[Sequence[int]]) -> int:
    """Exact fraction-free Bareiss determinant, with row pivoting."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("determinant requires a square matrix")
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    sign, previous = 1, 1
    for k in range(n - 1):
        pivot_row = next((r for r in range(k, n) if a[r][k] != 0), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot - a[i][k] * a[k][j]
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError("Bareiss exact-division invariant failed")
                a[i][j] = quotient
        for i in range(k + 1, n):
            a[i][k] = 0
        previous = pivot
    return sign * a[n - 1][n - 1]


def sylvester_map(f: Sequence[int], g: Sequence[int]) -> list[list[int]]:
    """Matrix of (A,B) -> AF+BG, multipliers having degree d-1."""
    if len(f) != len(g) or len(f) < 2:
        raise ValueError("forms must have the same positive homogeneous degree")
    d = len(f) - 1
    matrix = [[0] * (2 * d) for _ in range(2 * d)]
    for j in range(d):
        for k in range(d + 1):
            matrix[j + k][j] = f[k]
            matrix[j + k][d + j] = g[k]
    return matrix


def adjugate_column(matrix: Sequence[Sequence[int]], j: int) -> list[int]:
    n = len(matrix)
    if not 0 <= j < n or any(len(row) != n for row in matrix):
        raise ValueError("invalid matrix or adjugate column")
    # adj(S)[i,j] is cofactor(S)[j,i], not cofactor(S)[i,j].
    return [(-1) ** (i + j) * determinant([
                [matrix[r][c] for c in range(n) if c != i]
                for r in range(n) if r != j])
            for i in range(n)]


def verify_polynomial_certificate(cert: dict) -> bool:
    """Check two integral identities and their stated coefficient norm.

    A True result certifies the identities for the displayed F and G and
    nonzero R, with L their exact multiplier norm. This deliberately small
    verifier does NOT validate auxiliary A/B labels, a claimed Sylvester
    matrix/determinant, or provenance metadata. The EllipticCurve constructor
    supplies its duplication F,G explicitly before invoking this check.
    """
    try:
        f, g = cert["F"], cert["G"]
        d, resultant = len(f) - 1, cert["R"]
        if (len(g) != d + 1 or d < 1 or not isinstance(resultant, int)
                or resultant == 0 or not isinstance(cert["L"], int)):
            return False
        ax, bx, az, bz = (cert[name] for name in ("A_X", "B_X", "A_Z", "B_Z"))
        if any(len(v) != d for v in (ax, bx, az, bz)):
            return False
        if not all(isinstance(c, int) for v in (f, g, ax, bx, az, bz) for c in v):
            return False
        left_x = poly_add(poly_mul(ax, f), poly_mul(bx, g))
        left_z = poly_add(poly_mul(az, f), poly_mul(bz, g))
        norm = max(sum(map(abs, ax)) + sum(map(abs, bx)),
                   sum(map(abs, az)) + sum(map(abs, bz)))
        return (left_x == [resultant] + [0] * (2 * d - 1)
                and left_z == [0] * (2 * d - 1) + [resultant]
                and norm == cert["L"] and norm >= 1)
    except (KeyError, TypeError, ValueError):
        return False


@dataclass(frozen=True)
class EllipticCurve:
    """The nonsingular integral short Weierstrass equation y²=x³+A*x+B."""

    A: int
    B: int

    def __post_init__(self) -> None:
        if not isinstance(self.A, int) or not isinstance(self.B, int):
            raise TypeError("A and B must be integers")
        if self.discriminant == 0:
            raise ValueError("the cubic is singular")

    @property
    def discriminant(self) -> int:
        return -16 * (4 * self.A ** 3 + 27 * self.B ** 2)

    def contains(self, p: Point) -> bool:
        if p is None:
            return True
        try:
            x, y = map(Fraction, p)
        except (ValueError, TypeError, ZeroDivisionError):
            return False
        return y * y == x * x * x + self.A * x + self.B

    def point(self, x, y) -> Point:
        p = (Fraction(x), Fraction(y))
        if not self.contains(p):
            raise ValueError("coordinates do not lie on this curve")
        return p

    def _check(self, p: Point) -> None:
        if not self.contains(p):
            raise ValueError("input is not a point on this curve")

    def neg(self, p: Point) -> Point:
        self._check(p)
        if p is None:
            return None
        return (Fraction(p[0]), -Fraction(p[1]))

    def add(self, p: Point, q: Point) -> Point:
        self._check(p)
        self._check(q)
        if p is None:
            return None if q is None else (Fraction(q[0]), Fraction(q[1]))
        if q is None:
            return (Fraction(p[0]), Fraction(p[1]))
        x, y = map(Fraction, p)
        u, v = map(Fraction, q)
        if x == u:
            if y + v == 0:
                return None
            slope = (3 * x * x + self.A) / (2 * y)
        else:
            slope = (v - y) / (u - x)
        xx = slope * slope - x - u
        yy = slope * (x - xx) - y
        return (xx, yy)

    def sub(self, p: Point, q: Point) -> Point:
        return self.add(p, self.neg(q))

    def mul(self, n: int, p: Point) -> Point:
        self._check(p)
        if not isinstance(n, int):
            raise TypeError("the scalar must be an integer")
        if n < 0:
            n, p = -n, self.neg(p)
        acc = None
        while n:
            if n & 1:
                acc = self.add(acc, p)
            p = self.add(p, p)
            n //= 2
        return acc

    def iter_points(self, max_height: int) -> Iterator[Point]:
        """All points with x-height <= max_height, each exactly once.

        Integral coefficients imply x=a/d², y=b/d³, d>0,
        gcd(a,d)=1. The equation is b²=a³+A*a*d⁴+B*d⁶.
        Thus d<=isqrt(M), |a|<=M suffice. The exact square-root
        computation replaces a scan over |b|<= (1+|A|+|B|)*M².
        This deliberately generous bound is valid for M>=1.
        """
        if not isinstance(max_height, int):
            raise TypeError("the height bound must be an integer")
        if max_height < 0:
            raise ValueError("the height bound must be nonnegative")
        if max_height == 0:
            return
        yield None
        for d in range(1, isqrt(max_height) + 1):
            d2, d3 = d * d, d * d * d
            for a in range(-max_height, max_height + 1):
                if gcd(a, d) != 1:
                    continue
                square = a ** 3 + self.A * a * d ** 4 + self.B * d ** 6
                if square < 0:
                    continue
                b = isqrt(square)
                if b * b != square:
                    continue
                yield (Fraction(a, d2), Fraction(b, d3))
                if b:
                    yield (Fraction(a, d2), Fraction(-b, d3))

    def enumerate_points(self, max_height: int) -> list[Point]:
        return list(self.iter_points(max_height))

    def duplication_certificate(self, normalize: bool = True) -> dict:
        """Compute and verify the two degree-seven Bezout identities.

        By default divide both identity columns and their common R by the
        gcd of all their entries and R. This preserves integral identities
        and can substantially improve L. Raw determinant/adjugate metadata
        is retained separately; normalize=False selects the raw identities.
        """
        a, b = self.A, self.B
        f = [1, 0, -2 * a, -8 * b, a * a]
        g = [0, 4, 0, 4 * a, 4 * b]
        matrix = sylvester_map(f, g)
        resultant = determinant(matrix)
        if resultant == 0:
            raise ArithmeticError("nonsingular doubling map has zero resultant")
        cx, cz = adjugate_column(matrix, 0), adjugate_column(matrix, 7)
        factor = abs(resultant)
        for entry in cx + cz:
            factor = gcd(factor, abs(entry))
        if not normalize:
            factor = 1
        nx, nz = [c // factor for c in cx], [c // factor for c in cz]
        cert = {
            "A": a, "B": b, "discriminant": self.discriminant,
            "coefficient_order": "descending X exponent; complementary Z exponent",
            "F": f, "G": g, "S": matrix,
            "sylvester_determinant": resultant,
            "raw_adjugate_columns": {"X": cx, "Z": cz},
            "normalization_factor": factor,
            "R": resultant // factor,
            "A_X": nx[:4], "B_X": nx[4:],
            "A_Z": nz[:4], "B_Z": nz[4:],
            "L": max(sum(map(abs, nx)), sum(map(abs, nz))),
            "upper_height_coefficient": max(sum(map(abs, f)), sum(map(abs, g))),
        }
        if not verify_polynomial_certificate(cert):
            raise ArithmeticError("computed polynomial certificate is invalid")
        return cert

    def translation_constant(self, representative: Point) -> int:
        """T_R for H(P-R) <= T_R H(P)^2, with exceptional branches covered."""
        self._check(representative)
        if representative is None:
            return 1
        size = 1 + abs(self.A) + abs(self.B)
        return max(4 * size ** 2 * x_height(representative) ** 2,
                   x_height(self.mul(2, representative)), 1)

    def descent_data(self, representatives: Sequence[Point]) -> dict:
        """Compute constants; this does NOT verify quotient coverage."""
        if not representatives:
            raise ValueError("at least one actual representative is required")
        cert = self.duplication_certificate()
        constants = [self.translation_constant(r) for r in representatives]
        maximum = max(constants)
        c = ceil_log2(cert["L"] * maximum) + 2
        return {"L": cert["L"], "T": constants, "T_max": maximum, "C": c,
                "representatives": [point_text(r) for r in representatives],
                "coverage_verified": False}

    def halves(self, target: Point) -> list[Point]:
        """Return exactly all rational Q satisfying [2]Q=target.

        For target=(u/v,w), reduced v>0, rational x(Q) is a root of
          v*X^4 - 4u*X^3 - 2A*v*X^2
          + (-8B*v-4A*u)*X + A^2*v-4B*u.
        Rational-root and exact-square searches are finite. Exact doubling
        removes roots with the wrong y sign and any exceptional candidate.
        For target=O, the answer is O and the rational cubic roots with y=0.
        No Mordell--Weil theorem or coset representatives are assumed here.
        """
        self._check(target)
        if target is None:
            return [None] + [(x, Fraction(0))
                             for x in rational_roots([self.B, self.A, 0, 1])]
        x_target = Fraction(target[0])
        u, v = x_target.numerator, x_target.denominator
        a, b = self.A, self.B
        coefficients = [a * a * v - 4 * b * u,
                        -8 * b * v - 4 * a * u,
                        -2 * a * v, -4 * u, v]
        result = []
        for x in rational_roots(coefficients):
            for y in rational_square_roots(x ** 3 + a * x + b):
                q = (x, y)
                if self.mul(2, q) == target:
                    result.append(q)
        return result

    def division_by_representatives(
        self, p: Point, representatives: Sequence[Point]
    ) -> Optional[tuple[int, Point]]:
        """Finite exact selector, complete conditional on the supplied cover.

        Unlike bounded_division_search, this uses the rational-root theorem
        instead of enumerating every point under a large height cutoff.
        None means no displayed representative covers this particular p.
        """
        self._check(p)
        for i, r in enumerate(representatives):
            candidates = self.halves(self.sub(p, r))
            if candidates:
                return i, candidates[0]
        return None

    def bounded_division_search(
        self, p: Point, representatives: Sequence[Point]
    ) -> Optional[tuple[int, Point]]:
        """Search explicitly below H(Q)<=2**(h(P)+C) for P=2Q+R_i.

        This is finite but usually far too costly to run. If representatives
        really cover E(Q)/2E(Q), the report proves that this search succeeds.
        Without that hypothesis it may return None. The implementation never
        treats failure or sampled success as proof of the universal cover.
        """
        self._check(p)
        data = self.descent_data(representatives)
        bound = 1 << (integer_height(p) + data["C"])
        targets = [self.sub(p, r) for r in representatives]
        for q in self.iter_points(bound):
            double = self.mul(2, q)
            for i, target in enumerate(targets):
                if double == target:
                    return i, q
        return None


if __name__ == "__main__":
    import json
    curve = EllipticCurve(-1, 0)
    print(json.dumps(curve.duplication_certificate(), indent=2))
    print("E1 points through x-height 256:",
          [point_text(p) for p in curve.enumerate_points(256)])
