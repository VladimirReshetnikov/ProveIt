#!/usr/bin/env python3
"""Exact finite reference implementation for certified Zariski descent.

This module is deliberately elementary.  It implements the finite arithmetic
algorithms used in the accompanying report:

* explicit powers of a finite principal-cover certificate;
* exact gluing over a finite principal cover, including zero-divisor examples;
* polynomial ideal-membership certificate checking;
* the two-chart Cech normal form for O(d) on P^1;
* the monomial-wise contracting homotopy used for O(d) on P^n.

It is regression evidence for the algorithms, not an iPRA proof checker.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from math import factorial, comb
from random import Random
from typing import Dict, Iterable, Iterator, List, Mapping, MutableMapping, Sequence, Tuple


class Ring:
    """Minimal exact commutative-ring interface used by the finite algorithms."""

    def zero(self) -> int:
        return self.from_int(0)

    def one(self) -> int:
        return self.from_int(1)

    def from_int(self, n: int) -> int:
        raise NotImplementedError

    def add(self, a: int, b: int) -> int:
        raise NotImplementedError

    def neg(self, a: int) -> int:
        raise NotImplementedError

    def mul(self, a: int, b: int) -> int:
        raise NotImplementedError

    def eq(self, a: int, b: int) -> bool:
        raise NotImplementedError

    def sub(self, a: int, b: int) -> int:
        return self.add(a, self.neg(b))

    def pow(self, a: int, n: int) -> int:
        if n < 0:
            raise ValueError("ring powers require n >= 0")
        out = self.one()
        base = a
        k = n
        while k:
            if k & 1:
                out = self.mul(out, base)
            base = self.mul(base, base)
            k >>= 1
        return out

    def sum(self, xs: Iterable[int]) -> int:
        out = self.zero()
        for x in xs:
            out = self.add(out, x)
        return out


class IntegerRing(Ring):
    def from_int(self, n: int) -> int:
        return n

    def add(self, a: int, b: int) -> int:
        return a + b

    def neg(self, a: int) -> int:
        return -a

    def mul(self, a: int, b: int) -> int:
        return a * b

    def eq(self, a: int, b: int) -> bool:
        return a == b


@dataclass(frozen=True)
class ModRing(Ring):
    modulus: int

    def __post_init__(self) -> None:
        if self.modulus <= 0:
            raise ValueError("modulus must be positive")

    def from_int(self, n: int) -> int:
        return n % self.modulus

    def add(self, a: int, b: int) -> int:
        return (a + b) % self.modulus

    def neg(self, a: int) -> int:
        return (-a) % self.modulus

    def mul(self, a: int, b: int) -> int:
        return (a * b) % self.modulus

    def eq(self, a: int, b: int) -> bool:
        return (a - b) % self.modulus == 0


def weak_compositions(total: int, parts: int) -> Iterator[Tuple[int, ...]]:
    """Enumerate all alpha in N^parts with sum(alpha) = total."""
    if total < 0 or parts <= 0:
        raise ValueError("total >= 0 and parts > 0 required")
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in weak_compositions(total - first, parts - 1):
            yield (first,) + rest


def multinomial(alpha: Sequence[int]) -> int:
    total = sum(alpha)
    out = factorial(total)
    for a in alpha:
        out //= factorial(a)
    return out


def verify_unit_cover(
    ring: Ring, f: Sequence[int], c: Sequence[int]
) -> bool:
    if len(f) == 0 or len(f) != len(c):
        return False
    lhs = ring.sum(ring.mul(ci, fi) for ci, fi in zip(c, f))
    return ring.eq(lhs, ring.one())


def power_cover_coefficients(
    ring: Ring, f: Sequence[int], c: Sequence[int], exponent: int
) -> List[int]:
    """Construct d_i with sum_i d_i f_i^exponent = 1.

    The input must satisfy sum_i c_i f_i = 1.  For exponent N >= 1, expand
    (sum c_i f_i)^M with M = r(N-1)+1.  Every exponent vector of total M
    has a component at least N; assign the term to its least such component
    and factor f_i^N.
    """
    if exponent < 1:
        raise ValueError("exponent must be at least 1")
    if not verify_unit_cover(ring, f, c):
        raise ValueError("invalid unit-ideal cover certificate")
    r = len(f)
    M = r * (exponent - 1) + 1
    d = [ring.zero() for _ in range(r)]
    for alpha in weak_compositions(M, r):
        chosen = next((i for i, a in enumerate(alpha) if a >= exponent), None)
        if chosen is None:
            raise AssertionError("pigeonhole invariant failed")
        coeff = ring.from_int(multinomial(alpha))
        for j in range(r):
            coeff = ring.mul(coeff, ring.pow(c[j], alpha[j]))
            f_exp = alpha[j] - exponent if j == chosen else alpha[j]
            coeff = ring.mul(coeff, ring.pow(f[j], f_exp))
        d[chosen] = ring.add(d[chosen], coeff)
    return d


def verify_power_cover(
    ring: Ring, f: Sequence[int], d: Sequence[int], exponent: int
) -> bool:
    if len(f) != len(d) or exponent < 0:
        return False
    lhs = ring.sum(
        ring.mul(di, ring.pow(fi, exponent)) for di, fi in zip(d, f)
    )
    return ring.eq(lhs, ring.one())


@dataclass(frozen=True)
class LocalFraction:
    numerator: int
    denominator_exponent: int


@dataclass(frozen=True)
class GlueResult:
    global_section: int
    common_denominator_exponent: int
    cover_power_coefficients: Tuple[int, ...]
    homogenized_numerators: Tuple[int, ...]


def compatibility_holds(
    ring: Ring,
    fi: int,
    fj: int,
    ai: int,
    aj: int,
    common_exp: int,
    witness_exp: int,
) -> bool:
    """Check (fi*fj)^k * (fj^N ai - fi^N aj) = 0."""
    if common_exp < 0 or witness_exp < 0:
        return False
    difference = ring.sub(
        ring.mul(ring.pow(fj, common_exp), ai),
        ring.mul(ring.pow(fi, common_exp), aj),
    )
    killed = ring.mul(ring.pow(ring.mul(fi, fj), witness_exp), difference)
    return ring.eq(killed, ring.zero())


def glue_principal_cover(
    ring: Ring,
    f: Sequence[int],
    cover_coeffs: Sequence[int],
    local: Sequence[LocalFraction],
    compatibility_witnesses: Sequence[Sequence[int]],
) -> GlueResult:
    """Explicitly glue compatible local module sections over a principal cover.

    This implementation treats the module as the ring itself.  The proof and
    Lean outline use exactly the same formulas for any presented module.
    """
    r = len(f)
    if r == 0 or len(cover_coeffs) != r or len(local) != r:
        raise ValueError("cover arrays must be nonempty and have equal length")
    if len(compatibility_witnesses) != r or any(
        len(row) != r for row in compatibility_witnesses
    ):
        raise ValueError("compatibility witness matrix has the wrong shape")
    if not verify_unit_cover(ring, f, cover_coeffs):
        raise ValueError("invalid cover certificate")
    if any(s.denominator_exponent < 0 for s in local):
        raise ValueError("negative denominator exponent")

    N = max(s.denominator_exponent for s in local)
    a = [
        ring.mul(
            ring.pow(f[i], N - local[i].denominator_exponent),
            local[i].numerator,
        )
        for i in range(r)
    ]

    for i in range(r):
        for j in range(r):
            k = compatibility_witnesses[i][j]
            if not compatibility_holds(ring, f[i], f[j], a[i], a[j], N, k):
                raise ValueError(f"compatibility failed for ({i},{j})")

    K = max(max(row) for row in compatibility_witnesses)
    q = max(1, N + K)
    b = [ring.mul(ring.pow(f[i], q - N), a[i]) for i in range(r)]

    # Pairwise cross relation at the common exponent q.
    for i in range(r):
        for j in range(r):
            lhs = ring.mul(ring.pow(f[j], q), b[i])
            rhs = ring.mul(ring.pow(f[i], q), b[j])
            if not ring.eq(lhs, rhs):
                raise AssertionError("cleared compatibility invariant failed")

    d = power_cover_coefficients(ring, f, cover_coeffs, q)
    global_section = ring.sum(ring.mul(di, bi) for di, bi in zip(d, b))

    # Verify every restriction.  This equation witnesses equality of
    # global_section/1 and b_j/f_j^q in A_{f_j}.
    for j in range(r):
        lhs = ring.mul(ring.pow(f[j], q), global_section)
        if not ring.eq(lhs, b[j]):
            raise AssertionError(f"gluing equation failed on chart {j}")

    return GlueResult(global_section, q, tuple(d), tuple(b))


# ---------------------------------------------------------------------------
# Sparse univariate integer polynomials and ideal certificates
# ---------------------------------------------------------------------------

Poly = Dict[int, int]


def poly_clean(p: Mapping[int, int]) -> Poly:
    return {e: a for e, a in p.items() if a != 0}


def poly_add(p: Mapping[int, int], q: Mapping[int, int]) -> Poly:
    out: MutableMapping[int, int] = dict(p)
    for e, a in q.items():
        out[e] = out.get(e, 0) + a
    return poly_clean(out)


def poly_neg(p: Mapping[int, int]) -> Poly:
    return {e: -a for e, a in p.items() if a != 0}


def poly_sub(p: Mapping[int, int], q: Mapping[int, int]) -> Poly:
    return poly_add(p, poly_neg(q))


def poly_mul(p: Mapping[int, int], q: Mapping[int, int]) -> Poly:
    out: MutableMapping[int, int] = {}
    for e, a in p.items():
        for f, b in q.items():
            out[e + f] = out.get(e + f, 0) + a * b
    return poly_clean(out)


def verify_ideal_certificate(
    p: Mapping[int, int],
    q: Mapping[int, int],
    generators: Sequence[Mapping[int, int]],
    multipliers: Sequence[Mapping[int, int]],
) -> bool:
    """Verify p-q = sum h_i g_i exactly coefficientwise."""
    if len(generators) != len(multipliers):
        return False
    rhs: Poly = {}
    for g, h in zip(generators, multipliers):
        rhs = poly_add(rhs, poly_mul(h, g))
    return poly_clean(poly_sub(p, q)) == poly_clean(rhs)


# ---------------------------------------------------------------------------
# Laurent polynomials and the P^1 Cech complex for O(d)
# ---------------------------------------------------------------------------

Laurent = Dict[int, int]


def laurent_clean(p: Mapping[int, int]) -> Laurent:
    return {e: a for e, a in p.items() if a != 0}


def laurent_add(p: Mapping[int, int], q: Mapping[int, int]) -> Laurent:
    return poly_add(p, q)


def cech_delta_p1(d: int, a: Mapping[int, int], b: Mapping[int, int]) -> Laurent:
    """delta(a,b)=a(t)-t^d b(t^{-1}); a,b are ordinary polynomials."""
    if any(e < 0 for e in a) or any(e < 0 for e in b):
        raise ValueError("a and b must be ordinary polynomials")
    out: MutableMapping[int, int] = dict(a)
    for j, coeff in b.items():
        e = d - j
        out[e] = out.get(e, 0) - coeff
    return laurent_clean(out)


@dataclass(frozen=True)
class CechNormalFormP1:
    chart_zero: Laurent
    chart_one: Laurent
    obstruction: Laurent


def cech_normal_form_p1(d: int, cocycle: Mapping[int, int]) -> CechNormalFormP1:
    """Split c = delta(a,b) + middle with middle supported in d < e < 0."""
    a: Laurent = {}
    b: Laurent = {}
    middle: Laurent = {}
    for e, coeff in laurent_clean(cocycle).items():
        if e >= 0:
            a[e] = coeff
        elif e <= d:
            b[d - e] = -coeff
        else:
            middle[e] = coeff
    reconstructed = laurent_add(cech_delta_p1(d, a, b), middle)
    if laurent_clean(reconstructed) != laurent_clean(cocycle):
        raise AssertionError("P1 normal-form reconstruction failed")
    if any(not (d < e < 0) for e in middle):
        raise AssertionError("P1 obstruction support invariant failed")
    return CechNormalFormP1(a, b, middle)


def p1_h0_pair(d: int, coeffs: Sequence[int]) -> Tuple[Laurent, Laurent]:
    """Create the compatible chart pair for a degree-d homogeneous section."""
    expected = max(d + 1, 0)
    if len(coeffs) != expected:
        raise ValueError(f"expected {expected} coefficients")
    if d < 0:
        return {}, {}
    a = {e: coeffs[e] for e in range(d + 1) if coeffs[e] != 0}
    b = {j: coeffs[d - j] for j in range(d + 1) if coeffs[d - j] != 0}
    if cech_delta_p1(d, a, b):
        raise AssertionError("constructed global section is not compatible")
    return a, b


def projective_space_cohomology_ranks(n: int, d: int) -> Tuple[int, ...]:
    """Ranks of H^q(P^n,O(d)) for a free coefficient ring."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    ranks = [0] * (n + 1)
    if d >= 0:
        ranks[0] = comb(n + d, n)
    if d <= -n - 1:
        ranks[n] = comb(-d - 1, n)
    return tuple(ranks)


# ---------------------------------------------------------------------------
# Monomial-wise Cech contracting homotopy on P^n
# ---------------------------------------------------------------------------

Subset = Tuple[int, ...]
Matrix = List[List[int]]


def basis_subsets(n: int, neg: frozenset[int], degree: int) -> List[Subset]:
    """Basis in C^degree: subsets of size degree+1 containing neg."""
    if degree < 0 or degree > n:
        return []
    return [
        tuple(s)
        for s in combinations(range(n + 1), degree + 1)
        if neg.issubset(s)
    ]


def differential_matrix(n: int, neg: frozenset[int], p: int) -> Matrix:
    """Matrix d:C^p -> C^(p+1) for one exponent-vector summand."""
    src = basis_subsets(n, neg, p)
    dst = basis_subsets(n, neg, p + 1)
    src_index = {s: i for i, s in enumerate(src)}
    mat = [[0 for _ in src] for _ in dst]
    for row, J in enumerate(dst):
        for a in range(len(J)):
            I = J[:a] + J[a + 1 :]
            col = src_index.get(I)
            if col is not None:
                mat[row][col] += -1 if a % 2 else 1
    return mat


def homotopy_matrix(n: int, neg: frozenset[int], p: int, fixed: int) -> Matrix:
    """Matrix h:C^p -> C^(p-1) obtained by inserting fixed.

    Here p is the source cochain degree.  The target degree is p-1.
    """
    src = basis_subsets(n, neg, p)
    dst = basis_subsets(n, neg, p - 1)
    src_index = {s: i for i, s in enumerate(src)}
    mat = [[0 for _ in src] for _ in dst]
    for row, I in enumerate(dst):
        if fixed in I:
            continue
        J_list = sorted(I + (fixed,))
        J = tuple(J_list)
        col = src_index.get(J)
        if col is None:
            continue
        pos = J.index(fixed)
        mat[row][col] = -1 if pos % 2 else 1
    return mat


def mat_mul(A: Matrix, B: Matrix) -> Matrix:
    if not A:
        return []
    if not B:
        # If dimensions are genuinely zero, caller handles separately.
        return [[0] * 0 for _ in range(len(A))]
    if len(A[0]) != len(B):
        raise ValueError("matrix dimension mismatch")
    return [
        [sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
        for i in range(len(A))
    ]


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[0 for _ in range(cols)] for _ in range(rows)]


def compose_matrix(A: Matrix, A_rows: int, A_cols: int, B: Matrix, B_rows: int, B_cols: int) -> Matrix:
    """Multiply A*B while retaining dimensions of empty matrices."""
    if A_cols != B_rows:
        raise ValueError("matrix dimension mismatch")
    if A_rows == 0 or B_cols == 0:
        return zero_matrix(A_rows, B_cols)
    out = zero_matrix(A_rows, B_cols)
    for i in range(A_rows):
        for k in range(A_cols):
            aik = A[i][k]
            if aik:
                for j in range(B_cols):
                    out[i][j] += aik * B[k][j]
    return out


def matrix_add(A: Matrix, B: Matrix, rows: int, cols: int) -> Matrix:
    return [[A[i][j] + B[i][j] for j in range(cols)] for i in range(rows)]


def identity_matrix(n: int) -> Matrix:
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def check_contracting_homotopy(n: int, neg: frozenset[int]) -> bool:
    """Check dh+hd=id when neg is nonempty proper or empty with fixed chosen.

    For the projective-space proof, the mixed-sign case has neg a proper,
    nonempty subset.  The same contraction also applies to neg=empty in
    positive degrees, but degree zero has the expected cohomology.
    """
    if n < 0 or neg == frozenset(range(n + 1)):
        return False
    fixed = next(i for i in range(n + 1) if i not in neg)
    for p in range(n + 1):
        Cp = basis_subsets(n, neg, p)
        dim_p = len(Cp)
        if dim_p == 0:
            continue

        # h_{p+1} d_p : C^p -> C^p
        dim_p1 = len(basis_subsets(n, neg, p + 1))
        d_p = differential_matrix(n, neg, p) if p < n else zero_matrix(0, dim_p)
        h_p1 = homotopy_matrix(n, neg, p + 1, fixed) if p + 1 <= n else zero_matrix(dim_p, 0)
        hd = compose_matrix(h_p1, dim_p, dim_p1, d_p, dim_p1, dim_p)

        # d_{p-1} h_p : C^p -> C^p
        dim_pm1 = len(basis_subsets(n, neg, p - 1))
        h_p = homotopy_matrix(n, neg, p, fixed) if p >= 1 else zero_matrix(0, dim_p)
        d_pm1 = differential_matrix(n, neg, p - 1) if p >= 1 else zero_matrix(dim_p, 0)
        dh = compose_matrix(d_pm1, dim_p, dim_pm1, h_p, dim_pm1, dim_p)

        total = matrix_add(hd, dh, dim_p, dim_p)
        expected = identity_matrix(dim_p)
        if neg == frozenset() and p == 0:
            # The augmented-simplex contraction leaves the constant H^0 class.
            # We do not use this case for the mixed-sign acyclicity theorem.
            continue
        if total != expected:
            return False
    return True


def run_validation() -> dict:
    Z = IntegerRing()
    Z12 = ModRing(12)

    power_checks: List[dict] = []
    for exponent in range(1, 7):
        f = [2, 3]
        c = [-1, 1]
        d = power_cover_coefficients(Z, f, c, exponent)
        ok = verify_power_cover(Z, f, d, exponent)
        if not ok:
            raise AssertionError("integer power cover failed")
        power_checks.append({"ring": "Z", "exponent": exponent, "coefficients": d})

    for exponent in range(1, 6):
        f = [3, 4]
        c = [3, 1]
        d = power_cover_coefficients(Z12, f, c, exponent)
        ok = verify_power_cover(Z12, f, d, exponent)
        if not ok:
            raise AssertionError("Z/12 power cover failed")
        power_checks.append({"ring": "Z/12", "exponent": exponent, "coefficients": d})

    glue_Z = glue_principal_cover(
        Z,
        f=[2, 3],
        cover_coeffs=[-1, 1],
        local=[LocalFraction(34, 1), LocalFraction(153, 2)],
        compatibility_witnesses=[[0, 0], [0, 0]],
    )
    if glue_Z.global_section != 17:
        raise AssertionError("integer gluing did not recover 17")

    # A genuine zero-divisor/localization test.  In Z/12, the two local
    # numerators 9 and 8 represent the same global element 5 because
    # 3*(9-5)=0 and 4*(8-5)=0.  On the overlap, (3*4)^1 kills every difference.
    glue_Z12 = glue_principal_cover(
        Z12,
        f=[3, 4],
        cover_coeffs=[3, 1],
        local=[LocalFraction(9, 0), LocalFraction(8, 0)],
        compatibility_witnesses=[[0, 1], [1, 0]],
    )
    if not Z12.eq(glue_Z12.global_section, 5):
        raise AssertionError("Z/12 gluing did not recover the unique global class 5")

    # Quotient-ring equality certificate: x^4 = 4 in Z[x]/(x^2-2).
    p = {4: 1}
    q = {0: 4}
    g = [{2: 1, 0: -2}]
    h = [{2: 1, 0: 2}]
    ideal_ok = verify_ideal_certificate(p, q, g, h)
    if not ideal_ok:
        raise AssertionError("ideal-membership certificate failed")

    rng = Random(20261115)
    p1_checks = 0
    for d in range(-7, 8):
        for _ in range(80):
            lo = rng.randint(-12, -1)
            hi = rng.randint(0, 12)
            c = {e: rng.randint(-9, 9) for e in range(lo, hi + 1)}
            nf = cech_normal_form_p1(d, c)
            if any(not (d < e < 0) for e in nf.obstruction):
                raise AssertionError("bad P1 normal form")
            p1_checks += 1
        if d >= 0:
            coeffs = [rng.randint(-5, 5) for _ in range(d + 1)]
            p1_h0_pair(d, coeffs)
        else:
            p1_h0_pair(d, [])

    homotopy_checks = 0
    for n in range(1, 7):
        universe = range(n + 1)
        for size in range(1, n + 1):
            for neg_tuple in combinations(universe, size):
                neg = frozenset(neg_tuple)
                if not check_contracting_homotopy(n, neg):
                    raise AssertionError(f"contracting homotopy failed: n={n}, neg={neg}")
                homotopy_checks += 1

    rank_table = {
        f"n={n},d={d}": projective_space_cohomology_ranks(n, d)
        for n in range(1, 5)
        for d in range(-8, 9)
    }

    return {
        "power_cover_cases": len(power_checks),
        "power_cover_examples": power_checks,
        "gluing_integer": {
            "global": glue_Z.global_section,
            "common_exponent": glue_Z.common_denominator_exponent,
            "power_coefficients": glue_Z.cover_power_coefficients,
        },
        "gluing_Zmod12": {
            "global": glue_Z12.global_section,
            "common_exponent": glue_Z12.common_denominator_exponent,
            "power_coefficients": glue_Z12.cover_power_coefficients,
        },
        "ideal_membership_certificate": ideal_ok,
        "p1_normal_form_cases": p1_checks,
        "projective_contracting_homotopy_cases": homotopy_checks,
        "rank_table": rank_table,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_validation(), indent=2, sort_keys=True))
