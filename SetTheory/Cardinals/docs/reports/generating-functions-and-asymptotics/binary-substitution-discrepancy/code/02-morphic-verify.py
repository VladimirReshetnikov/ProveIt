#!/usr/bin/env python3
"""Exact and independent checks for the quadratic morphic-word report.

Only the Python standard library is used.  Algebraic numbers are represented
as A + B*sqrt(D) with rational A,B, so every asserted inequality is decided
without floating point.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, getcontext
from fractions import Fraction
import json
from pathlib import Path
from typing import Iterable

getcontext().prec = 60
ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Quad:
    """An exact number A + B*sqrt(D), with A and B rational."""

    A: Fraction
    B: Fraction
    D: int

    @staticmethod
    def rational(x: int | Fraction, D: int) -> "Quad":
        return Quad(Fraction(x), Fraction(0), D)

    def _coerce(self, other: int | Fraction | "Quad") -> "Quad":
        if isinstance(other, Quad):
            if self.D != other.D:
                raise ValueError("different quadratic fields")
            return other
        return Quad.rational(other, self.D)

    def __add__(self, other: int | Fraction | "Quad") -> "Quad":
        other = self._coerce(other)
        return Quad(self.A + other.A, self.B + other.B, self.D)

    __radd__ = __add__

    def __neg__(self) -> "Quad":
        return Quad(-self.A, -self.B, self.D)

    def __sub__(self, other: int | Fraction | "Quad") -> "Quad":
        return self + (-self._coerce(other))

    def __rsub__(self, other: int | Fraction | "Quad") -> "Quad":
        return self._coerce(other) - self

    def __mul__(self, other: int | Fraction | "Quad") -> "Quad":
        other = self._coerce(other)
        return Quad(
            self.A * other.A + self.B * other.B * self.D,
            self.A * other.B + self.B * other.A,
            self.D,
        )

    __rmul__ = __mul__

    def inverse(self) -> "Quad":
        den = self.A * self.A - self.B * self.B * self.D
        if den == 0:
            raise ZeroDivisionError
        return Quad(self.A / den, -self.B / den, self.D)

    def __truediv__(self, other: int | Fraction | "Quad") -> "Quad":
        return self * self._coerce(other).inverse()

    def __rtruediv__(self, other: int | Fraction | "Quad") -> "Quad":
        return self._coerce(other) / self

    def sign(self) -> int:
        """Return -1, 0, or +1 exactly."""
        if self.B == 0:
            return (self.A > 0) - (self.A < 0)
        if self.B < 0:
            return -(-self).sign()
        # B > 0.
        if self.A >= 0:
            return 1
        lhs = self.B * self.B * self.D
        rhs = self.A * self.A
        return (lhs > rhs) - (lhs < rhs)

    def __lt__(self, other: int | Fraction | "Quad") -> bool:
        return (self - other).sign() < 0

    def __le__(self, other: int | Fraction | "Quad") -> bool:
        return (self - other).sign() <= 0

    def __gt__(self, other: int | Fraction | "Quad") -> bool:
        return (self - other).sign() > 0

    def __ge__(self, other: int | Fraction | "Quad") -> bool:
        return (self - other).sign() >= 0

    def decimal(self) -> Decimal:
        return Decimal(self.A.numerator) / Decimal(self.A.denominator) + (
            Decimal(self.B.numerator)
            / Decimal(self.B.denominator)
            * Decimal(self.D).sqrt()
        )

    def as_json(self) -> dict[str, object]:
        def f(x: Fraction) -> str:
            return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"

        return {"A": f(self.A), "B": f(self.B), "D": self.D, "decimal": str(self.decimal())}

    def __repr__(self) -> str:
        return f"Quad({self.A!s}, {self.B!s}, {self.D})"


def q_parameter(a: int, b: int) -> Quad:
    D = (b + 1) ** 2 + 4 * a
    square = 1
    p = 2
    while p * p <= D:
        while D % (p * p) == 0:
            D //= p * p
            square *= p
        p += 1
    return Quad(Fraction(-(b + 1), 2), Fraction(square, 2), D)


def substitute(word: bytes, a: int, b: int) -> bytes:
    image1 = b"1" + b"0" * a + b"1" * b
    return b"".join(b"1" if c == 48 else image1 for c in word)


def fixed_prefix(a: int, b: int, minimum_length: int) -> bytes:
    word = b"1"
    while len(word) < minimum_length:
        word = substitute(word, a, b)
    return word


def positions(word: bytes, letter: int, limit: int | None = None) -> list[int]:
    target = 48 + letter
    out: list[int] = []
    for i, c in enumerate(word, 1):
        if c == target:
            out.append(i)
            if limit is not None and len(out) >= limit:
                break
    return out


def position_error(letter: int, rank: int, pos: int, q: Quad) -> Quad:
    if letter == 1:
        # (1+q)n - position
        return (1 + q) * rank - pos
    # (1+1/q)n - position
    return (1 + 1 / q) * rank - pos


def candidate_extrema(a: int, b: int) -> tuple[Quad, Quad, Quad, Quad, Quad, Quad]:
    q = q_parameter(a, b)
    one = Quad.rational(1, q.D)
    C = (a - q) / (one - q * q)
    l0 = -q * (C + 1)
    u0 = C - 1
    l1 = -q * C
    u1 = C
    return q, C, l0, u0, l1, u1


def check_general_extrema(max_b: int = 14) -> int:
    checks = 0
    for b in range(1, max_b + 1):
        for a in range(1, b + 2):
            q, C, l0, u0, l1, u1 = candidate_extrema(a, b)
            assert 0 < q < 1
            # Basic algebraic identities.
            assert (q * q + (b + 1) * q - a).sign() == 0
            assert C * (1 - q * q) == a - q
            # Bellman extremum equations.
            assert l0 == -q * u1 - q
            assert u0 == -q * l1 + (a - 1 - q)
            assert u1 > u0
            assert l1 == -q * u1
            self_max = -q * l1 + a - q
            from_zero = -q * l0
            assert self_max == u1
            assert from_zero < u1
            checks += 12
    return checks


def assert_between(x: Quad, lo: Quad, hi: Quad) -> None:
    assert lo < x < hi, (x, lo, hi)


def scan_case(a: int, b: int, length: int, sharp: dict[int, tuple[Quad, Quad]]) -> dict[str, object]:
    q = q_parameter(a, b)
    word = fixed_prefix(a, b, length)
    results: dict[str, object] = {"generated_length": len(word), "scanned_length": length}
    for letter in (0, 1):
        rank = 0
        observed_min: Quad | None = None
        observed_max: Quad | None = None
        min_at = max_at = None
        lo, hi = sharp[letter]
        for pos, c in enumerate(word[:length], 1):
            if c == 48 + letter:
                rank += 1
                err = position_error(letter, rank, pos, q)
                assert_between(err, lo, hi)
                if observed_min is None or err < observed_min:
                    observed_min, min_at = err, (rank, pos)
                if observed_max is None or err > observed_max:
                    observed_max, max_at = err, (rank, pos)
        assert observed_min is not None and observed_max is not None
        results[f"letter_{letter}"] = {
            "terms_scanned": rank,
            "observed_min": observed_min.as_json(),
            "observed_min_at": min_at,
            "observed_max": observed_max.as_json(),
            "observed_max_at": max_at,
            "sharp_lower": lo.as_json(),
            "sharp_upper": hi.as_json(),
        }
    return results


def check_oeis_prefixes() -> int:
    checks = 0
    # A284368 and its zero positions A184485.
    expected_368 = bytes(int(x) + 48 for x in [
        1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,
        1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,
    ])
    w368 = fixed_prefix(1, 2, len(expected_368))
    assert w368[: len(expected_368)] == expected_368
    checks += len(expected_368)
    expected_zero_368 = [2,7,11,15,19,24,28,32,37,41,45,50,54,58,63,67,71,75,80,84,
                         88,93,97,101,106,110,114,118,123,127]
    assert positions(w368 if len(w368) >= expected_zero_368[-1] else fixed_prefix(1,2,130), 0, 30) == expected_zero_368
    checks += len(expected_zero_368)

    # A284369 and position sequences A284370/A284371.
    expected_369 = bytes(int(x) + 48 for x in [
        1,0,0,1,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,1,1,0,0,1,1,0,
        0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,0,0,1,1,0,
        0,1,1,0,0,1,1,0,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,0,0,1,
    ])
    w369 = fixed_prefix(2, 1, 160)
    assert w369[: len(expected_369)] == expected_369
    checks += len(expected_369)
    expected_zero_369 = [2,3,8,9,12,13,16,17,20,21,26,27,30,31,36,37,40,41,46,47,
                         50,51,56,57,60,61,64,65,68,69]
    expected_one_369 = [1,4,5,6,7,10,11,14,15,18,19,22,23,24,25,28,29,32,33,34,
                        35,38,39,42,43,44,45,48,49,52]
    assert positions(w369, 0, 30) == expected_zero_369
    assert positions(w369, 1, 30) == expected_one_369
    checks += 60
    return checks


def check_interval_tilings() -> int:
    checks = 0
    # A284368: four intervals tile S_1 exactly, and one image gives S_0.
    q, C, l0, u0, l1, u1 = candidate_extrema(1, 2)
    intervals = [
        (-q * u1, -q * l1),
        (-q * u0, -q * l0),
        (-q * u1 + 1 - 2*q, -q * l1 + 1 - 2*q),
        (-q * u1 + 1 - q, -q * l1 + 1 - q),
    ]
    assert intervals[0][0] == l1
    for left, right in zip(intervals, intervals[1:]):
        assert left[1] == right[0]
    assert intervals[-1][1] == u1
    assert (-q*u1-q, -q*l1-q) == (l0, u0)
    checks += 7

    # A284369: overlapping images cover both state intervals.
    q, C, l0, u0, l1, u1 = candidate_extrema(2, 1)
    z0 = (-q*u1-q, -q*l1-q)
    z1 = (-q*u1+1-q, -q*l1+1-q)
    assert z0[0] == l0 and z1[1] == u0 and z1[0] < z0[1]
    o0 = (-q*u1, -q*l1)
    ofrom0 = (-q*u0, -q*l0)
    omax = (-q*u1+2-q, -q*l1+2-q)
    assert o0[0] == l1 and omax[1] == u1
    assert ofrom0[0] < o0[1] and omax[0] < ofrom0[1]
    checks += 7
    return checks


def extremal_counts(a: int, b: int, count: int) -> list[dict[str, int]]:
    # c_{k+1}=M^2 c_k + (a,1)^T.
    m00, m01 = a, a * (b + 1)
    m10, m11 = b + 1, a + (b + 1) ** 2
    z = o = 0
    out = []
    for k in range(count):
        out.append({"k": k, "zeros": z, "ones": o, "length": z + o})
        z, o = m00*z + m01*o + a, m10*z + m11*o + 1
    return out


def main() -> None:
    checks = 0
    checks += check_general_extrema()
    checks += check_oeis_prefixes()
    checks += check_interval_tilings()

    # Exact sharp position-error endpoints.
    sqrt13 = Quad(Fraction(0), Fraction(1), 13)
    sharp368 = {
        1: ((sqrt13 - 5) / 3, (sqrt13 - 2) / 3),
        0: ((1 + sqrt13) / 3, (4 + sqrt13) / 3),
    }
    sqrt3 = Quad(Fraction(0), Fraction(1), 3)
    sharp369 = {
        1: (Quad.rational(-2, 3), 1 + sqrt3),
        0: (-(3 + sqrt3) / 2, 2 + sqrt3),
    }

    scan368 = scan_case(1, 2, 100_000, sharp368)
    scan369 = scan_case(2, 1, 100_000, sharp369)
    checks += sum(scan368[f"letter_{x}"]["terms_scanned"] for x in (0,1))
    checks += sum(scan369[f"letter_{x}"]["terms_scanned"] for x in (0,1))

    # Every tested value satisfies the original OEIS bounds as well.
    assert sharp368[0][0] > 1 and sharp368[0][1] < 3
    assert sharp368[1][0] > -1 and sharp368[1][1] < 1
    assert sharp369[0][0] > -3 and sharp369[0][1] < 4
    assert (sharp369[1][0] + 2).sign() == 0 and sharp369[1][1] < 3
    checks += 8

    report = {
        "method": "standard-library exact quadratic arithmetic plus literal substitution prefixes",
        "checks": checks,
        "general_parameter_pairs_checked": sum(b + 1 for b in range(1, 15)),
        "A284368_family": scan368,
        "A284369_family": scan369,
        "extremal_cycle_A284368": extremal_counts(1, 2, 10),
        "extremal_cycle_A284369": extremal_counts(2, 1, 11),
    }
    out = ROOT / "data" / "verification.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {checks:,} exact/counting checks")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
