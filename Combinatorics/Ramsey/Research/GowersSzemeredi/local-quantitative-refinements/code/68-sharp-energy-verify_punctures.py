#!/usr/bin/env python3
"""Exact finite consistency checks for sections/punctures.tex."""
import json
from functools import lru_cache


def rotate(mask, d, n):
    d %= n
    full = (1 << n) - 1
    if d == 0:
        return mask
    return ((mask << d) | (mask >> (n - d))) & full


def correlations(mask, n):
    return [(mask & rotate(mask, d, n)).bit_count() for d in range(n)]


def energy(mask, n):
    return sum(r*r for r in correlations(mask, n))


@lru_cache(maxsize=None)
def cosets(n):
    out = []
    for step in range(1, n+1):
        if n % step:
            continue
        H = sum(1 << a for a in range(0, n, step))
        for c in range(step):
            out.append((rotate(H, c, n), H))
    return out


counts = {"subsets": 0, "high_energy_subsets": 0,
          "remainder_checks": 0, "nested_checks": 0,
          "oriented_checks": 0, "nonzero_nested_checks": 0,
          "nonzero_oriented_checks": 0,
          "global_high_energy_subsets": 0, "global_nested_checks": 0,
          "global_oriented_checks": 0, "global_extra_outer_checks": 0,
          "global_nonunique_holes": 0, "global_nested_equalities": 0,
          "global_oriented_equalities": 0,
          "inner_endpoint_nested_checks": 0,
          "inner_endpoint_oriented_checks": 0,
          "inner_endpoint_nested_equalities": 0,
          "inner_endpoint_oriented_equalities": 0}


def check_global(mask, n, all_c, rs, defect):
    m = mask.bit_count()
    if 4*defect >= m**3:
        return
    counts["global_high_energy_subsets"] += 1
    H = sum(1 << d for d, v in enumerate(rs) if 2*v > m)
    assert any(H == sub for _, sub in all_c)
    hc = [(C, sub) for C, sub in all_c if sub == H]
    occupancies = [(mask & C).bit_count() for C, _ in hc]
    C, _ = max(hc, key=lambda item: (mask & item[0]).bit_count())
    p_max = (mask & C).bit_count()
    assert 2*p_max > m
    k = (mask ^ C).bit_count()
    assert 2*k < m
    t = (mask & ~C).bit_count()
    assert 4*t < m
    assert m*k*(m-k) <= defect
    S = sum(v*v for v in occupancies)
    frontier = k*m+2*(p_max*m-S)
    assert 0 <= 2*frontier < m*m
    assert defect*m >= frontier*(m*m-frontier)
    T, K = mask & ~C, C & ~mask
    eta = defect-m*k*(m-k)
    u = K.bit_count()
    assert 8*eta >= 3*t*m*m+8*(u**3-energy(K, n))
    for d, v in enumerate(rs):
        theta = defect-m*v*(m-v)
        if not ((H >> d) & 1):
            assert 8*theta >= k*m*m
    if not k:
        return
    hole_candidates = [(J, sub) for J, sub in all_c if J != C and J & ~C == 0]

    def classify_nested_equality():
        assert t == 0
        if eta == 0:
            assert any(J == K for J, _ in all_c)
            return
        inner_rs = correlations(K, n)
        inner_H = sum(1 << d for d, v in enumerate(inner_rs) if 2*v > u)
        inner_cosets = [(J, sub) for J, sub in all_c if sub == inner_H]
        D, _ = max(inner_cosets, key=lambda item: (K & item[0]).bit_count())
        J = D & ~K
        assert K == D & ~J
        assert J and any(J == C2 for C2, _ in all_c)
        assert D.bit_count() % J.bit_count() == 0
        assert D.bit_count() // J.bit_count() >= 4

    def classify_inner_endpoint():
        assert t == 0
        assert 4*(u**3-energy(K, n)) == u**3
        inner_rs = correlations(K, n)
        inner_H = sum(1 << d for d, v in enumerate(inner_rs) if 2*v > u)
        occupied = [J for J, sub in all_c if sub == inner_H and K & J]
        assert len(occupied) == 2
        assert occupied[0] | occupied[1] == K
        assert occupied[0].bit_count() == occupied[1].bit_count() == u//2
        first = (occupied[0] & -occupied[0]).bit_length()-1
        second = (occupied[1] & -occupied[1]).bit_length()-1
        assert not ((inner_H >> ((2*(second-first)) % n)) & 1)

    if 4*eta < k**3:
        edits = [(t+(K ^ J).bit_count(), J, sub) for J, sub in hole_candidates]
        best = min(z[0] for z in edits)
        winners = [z for z in edits if z[0] == best]
        assert 2*best < k
        assert k*best*(k-best) <= eta
        counts["global_nested_checks"] += 1
        counts["global_extra_outer_checks"] += 9*defect >= 2*m**3
        counts["global_nonunique_holes"] += len(winners) > 1
        if k*best*(k-best) == eta:
            classify_nested_equality()
            counts["global_nested_equalities"] += 1
    if 4*eta == k**3:
        edits = [(t+(K ^ J).bit_count(), J, sub) for J, sub in hole_candidates]
        best = min(z[0] for z in edits)
        assert 2*best <= k
        assert k*best*(k-best) <= eta
        counts["inner_endpoint_nested_checks"] += 1
        if 2*best == k:
            classify_inner_endpoint()
            counts["inner_endpoint_nested_equalities"] += 1
    for d, v in enumerate(rs):
        theta = defect-m*v*(m-v)
        if 4*theta >= k**3:
            continue
        assert (H >> d) & 1
        edits = [(t+(K ^ J).bit_count(), J, sub) for J, sub in hole_candidates]
        best = min(z[0] for z in edits)
        winners = [z for z in edits if z[0] == best]
        assert all(not ((sub >> d) & 1) for _, _, sub in winners)
        assert 2*best < k
        assert k*best*(k-best) <= theta
        counts["global_oriented_checks"] += 1
        if k*best*(k-best) == theta:
            assert theta == eta
            classify_nested_equality()
            counts["global_oriented_equalities"] += 1
    for d, v in enumerate(rs):
        theta = defect-m*v*(m-v)
        if 4*theta != k**3:
            continue
        assert (H >> d) & 1
        edits = [(t+(K ^ J).bit_count(), J, sub) for J, sub in hole_candidates]
        best = min(z[0] for z in edits)
        winners = [z for z in edits if z[0] == best]
        assert 2*best <= k
        assert all(not ((sub >> d) & 1) for _, _, sub in winners)
        counts["inner_endpoint_oriented_checks"] += 1
        if 2*best == k:
            assert theta == eta
            assert not (K & rotate(K, d, n))
            classify_inner_endpoint()
            counts["inner_endpoint_oriented_equalities"] += 1


def check(mask, n, all_remainders=False):
    counts["subsets"] += 1
    m = mask.bit_count()
    if not m:
        return
    all_c = cosets(n)
    rs = correlations(mask, n)
    ea = sum(v*v for v in rs)
    defect = m**3 - ea
    # Universal inequality, independently checked as input.
    for v in rs:
        assert defect >= m*v*(m-v)
    check_global(mask, n, all_c, rs, defect)

    def remainder(C):
        k = (mask ^ C).bit_count()
        T = mask & ~C
        K = C & ~mask
        t, u = T.bit_count(), K.bit_count()
        inside = mask & C
        b = inside.bit_count()
        assert ea <= energy(inside, n)+6*b*t*t+t**3
        eta = defect-m*k*(m-k)
        rhs = t*(2*m*m+k*k-(8*m+k)*t+6*t*t)+u**3-energy(K, n)
        assert eta >= rhs
        counts["remainder_checks"] += 1

    if all_remainders:
        for C, _ in all_c:
            remainder(C)
    if 9*defect >= 2*m**3:
        return
    counts["high_energy_subsets"] += 1
    H = sum(1 << d for d, v in enumerate(rs) if 2*v > m)
    assert any(H == sub for _, sub in all_c)
    hc = [(C, sub) for C, sub in all_c if sub == H]
    C, _ = max(hc, key=lambda item: (mask & item[0]).bit_count())
    k = (mask ^ C).bit_count()
    assert 3*k < m
    assert m*k*(m-k) <= defect
    distances = [(mask ^ J).bit_count() for J, _ in all_c]
    assert distances.count(min(distances)) == 1
    assert k == min(distances)
    remainder(C)
    T, K = mask & ~C, C & ~mask
    t = T.bit_count()
    rk, rt = correlations(K, n), correlations(T, n)
    eta = defect-m*k*(m-k)
    for d, v in enumerate(rs):
        theta = defect-m*v*(m-v)
        if (H >> d) & 1:
            z = rk[d]+rt[d]
            assert v == m-k+z
            assert theta == eta+m*z*(m-2*k+z)
        elif k:
            # theta/m^3 >= delta/6.
            assert 6*theta >= k*m*m
    if not k:
        return
    hole_candidates = [(J, sub) for J, sub in all_c if J != C and J & ~C == 0]
    if 9*eta < 2*k**3:
        edits = [(t+(K ^ J).bit_count(), J, sub) for J, sub in hole_candidates]
        best = min(z[0] for z in edits)
        winners = [z for z in edits if z[0] == best]
        assert len(winners) == 1
        assert 3*best < k
        assert k*best*(k-best) <= eta
        counts["nested_checks"] += 1
        counts["nonzero_nested_checks"] += bool(eta)
    for d, v in enumerate(rs):
        theta = defect-m*v*(m-v)
        if 9*theta >= 2*k**3:
            continue
        assert (H >> d) & 1
        oriented = [(t+(K ^ J).bit_count(), J, sub)
                    for J, sub in hole_candidates if not ((sub >> d) & 1)]
        assert oriented
        best = min(z[0] for z in oriented)
        assert 3*best < k
        assert k*best*(k-best) <= theta
        counts["oriented_checks"] += 1
        counts["nonzero_oriented_checks"] += bool(theta)


# Exhaustive small cyclic groups, including every proposed coset remainder
# through n=10. Larger groups verify the canonical remainder.
for n in range(1, 16):
    for mask in range(1, 1 << n):
        check(mask, n, all_remainders=(n <= 10))

# Sharp nonzero nested/oriented examples. These are too large for subset
# enumeration, so the whole pointwise correlation arrays are checked.
for R in (10, 11, 12):
    for r in (5, 6, 8, 9, 12, 16):
        n = R*r
        full = (1 << n)-1
        D = sum(1 << a for a in range(0, n, R))
        A = (full ^ D) | 1
        check(A, n)
        m = A.bit_count()
        k = r-1
        rs = correlations(A, n)
        defect = m**3-sum(v*v for v in rs)
        theta = defect-m*rs[1]*(m-rs[1])
        assert theta == (r-1)*(r-2)
        assert k*(k-1) == theta  # one edit attains exact profile

# Beyond the old 1/9 range: nested cosets in Z/25Z and products realized
# cyclically when the ambient index is five.
for R in (5, 6, 7, 8, 9):
    for r in (5, 6, 9, 12):
        n = R*r
        full = (1 << n)-1
        D = sum(1 << a for a in range(0, n, R))
        A = (full ^ D) | 1
        check(A, n)

# Both outer and inner extension beyond 2/9 are exercised here. In Z/12Z,
# K={3,6,9} has several nearest cosets: the global theorem must not claim
# uniqueness of its hole.
for r in (4, 5, 6, 7):
    R = 3
    n = R*r
    full = (1 << n)-1
    D = sum(1 << a for a in range(0, n, R))
    A = (full ^ D) | 1
    check(A, n)

# Strict, nonextremal profiles: remove a noncoset J from the subgroup hole.
# These checks have a genuine positive secondary energy remainder.
for R in (6, 10):
    for r in (17, 19):
        n = R*r
        full = (1 << n)-1
        D = sum(1 << a for a in range(0, n, R))
        J = 1 | (1 << R)
        A = (full ^ D) | J
        check(A, n)

# Nonzero outliers in a proper canonical outer coset. The inner normalized
# excess remains below 1/4; the coupled F estimate is strictly decreasing.
R, r = 5, 200
n = 2*R*r
C = sum(1 << a for a in range(0, n, 2))
D = sum(1 << a for a in range(0, n, 2*R))
for J in (0, 1 | (1 << (2*R))):
    A = (C ^ D) | J | (1 << 1)
    check(A, n)

# Inner quarter-endpoint attainment with nontrivial constituent subgroups.
# Quotient gaps of order eight and three are both included.
for quotient_order, h, gap in ((8, 3, 1), (8, 5, 1), (8, 6, 1),
                              (9, 2, 3), (9, 4, 3)):
    n = quotient_order*h
    full = (1 << n)-1
    L = sum(1 << a for a in range(0, n, quotient_order))
    K = L | rotate(L, gap, n)
    A = full ^ K
    check(A, n)

# Sharp uniqueness boundary (not covered by the strict theorem).
n, A = 4, 0b0111
m = A.bit_count()
assert energy(A, n) == 21
ds = [(A ^ C).bit_count() for C, _ in cosets(n)]
assert min(ds) == 1 and ds.count(1) >= 2

# The outer quarter endpoint cannot be included in canonical puncture repair.
n = 6
H = (1 << 0) | (1 << 3)
A = H | rotate(H, 1, n)
m = A.bit_count()
rs = correlations(A, n)
defect = m**3-sum(v*v for v in rs)
assert 4*defect == m**3
assert H & ~A == 0
k = (A ^ H).bit_count()
assert 2*k == m
assert defect-m*k*(m-k) == 0
assert defect-m*rs[1]*(m-rs[1]) == 0
assert A != H

print(json.dumps(counts, indent=2))
