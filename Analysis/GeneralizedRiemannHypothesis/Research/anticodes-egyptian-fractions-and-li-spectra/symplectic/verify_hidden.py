"""Reproduce the window table and small finite-field checks. Python 3.10+."""
from collections import Counter
from decimal import Decimal as Q, getcontext, ROUND_CEILING
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import prod


@lru_cache(maxsize=None)
def pivot_basis(vectors):
    """Canonical reduced binary basis, in descending pivot order."""
    basis = []
    for row in vectors:
        for b in basis:
            row = min(row, row ^ b)
        if row:
            basis = [min(b, b ^ row) for b in basis]
            basis.append(row)
            basis.sort(reverse=True)
    return tuple(basis)


def wedge(x, y, n):
    bits = []
    for i, j in combinations(range(n), 2):
        bits.append(((x >> i) & (y >> j) & 1) ^ ((x >> j) & (y >> i) & 1))
    return sum(b << i for i, b in enumerate(bits))


def value(form, row):
    return (form & row).bit_count() % 2


def matrix_rows(form, n):
    out = [0] * n
    for k, (i, j) in enumerate(combinations(range(n), 2)):
        if (form >> k) & 1:
            out[i] |= 1 << j
            out[j] |= 1 << i
    return tuple(out)


def check_small_planes():
    n = 4
    dim = 6
    pluecker = {wedge(x, y, n) for x, y in combinations(range(1, 2**n), 2)}
    nonsingular = {f for f in range(2**dim) if len(pivot_basis(matrix_rows(f, n))) == n}
    assert len(pluecker) == 35 and len(nonsingular) == 28
    for f in nonsingular:
        assert sum(not value(f, p) for p in pluecker) == 15
    # Arbitrary-precision counts of ordered t-tuples by their row span.
    counts = {(): 1}
    for t in range(1, 7):
        new_counts = Counter()
        for span, mass in counts.items():
            for row in pluecker:
                new_counts[pivot_basis((*span, row))] += mass
        counts = new_counts
        assert sum(counts.values()) == 35**t
        mean = 28 * Fraction(15, 35)**t
        total_z, distance = 0, Fraction(0)
        for span, mass in counts.items():
            z = sum(all(not value(f, row) for row in span) for f in nonsingular)
            total_z += mass * z
            distance += Fraction(mass, 35**t) * max(0, 1 - z / mean)
        assert Fraction(total_z, 35**t) == mean
        if t in (1, 2, 4, 5, 6):
            expected = {1: 0., 2: .11429, 4: .37280, 5: .66308, 6: .84036}[t]
            assert abs(float(distance) - expected) < .0000051
        print(f'F2, n=4, r=2, t={t}: exact TV {distance} = {float(distance):.7f}')
    # Test simultaneous nonsingularity for the dependent triple A,B,A+B,
    # using Pott--Schmidt--Zhou's exact finite formula at q=2, n=4.
    triples = sum((a ^ b) in nonsingular for a in nonsingular for b in nonsingular)
    assert triples == 28 * (49 - 5 + 4) // 4
    print('F2, n=4: ordered pairs with A, B, A+B nonsingular:', triples)


def check_three_dimensional_planes():
    n = 6
    planes = {pivot_basis(vectors) for vectors in combinations(range(1, 2**n), 3)}
    planes = {basis for basis in planes if len(basis) == 3}
    symplectic = sum(1 << k for k, (i, j) in enumerate(combinations(range(n), 2))
                     if i % 2 == 0 and j == i + 1)
    assert len(planes) == 1395
    observed = sum(all(not value(symplectic, wedge(x, y, n))
                       for x, y in combinations(basis, 2)) for basis in planes)
    probability = prod(Fraction(2**(n-j) - 2**j, 2**n - 2**j) for j in range(3))
    assert Fraction(observed, len(planes)) == probability
    print(f'F2, n=6, r=3: {observed} isotropic planes among {len(planes)}; p={probability}')


def compute_table(q, offsets):
    """Decimal evaluation with finite product cutoffs justified below."""
    getcontext().prec = 80
    field = Q(q)
    e = [Q(1)]
    for j in range(1, 241):
        e.append(e[-1] * (1-field**(-j)))
    delta = prod(1-field**(-j) for j in range(1, 241, 2))
    for s in offsets:
        mu = delta * field**(-s) / (field-1)
        tv, success, normalization = Q(0), Q(0), Q(0)
        for k in range(max(0, -s), 16):
            mass = field**(-k*(k+s)) * e[-1] / (e[k] * e[k+s])
            h = (q**k-1) // (q-1)
            p = (1-delta)**h
            normalization += mass
            success += mass * (1-p) / mu
            for z in range(min(h, int(mu.to_integral_value(rounding=ROUND_CEILING))-1)+1):
                tv += mass * (1-Q(z)/mu) * p
                p *= (Q(h-z) / (z+1)) * delta / (1-delta)
        # For q>=2, |s|<=3, the omitted dimension tail is
        # <= e_infty^{-2} sum_{k>=16} q^{-k(k+s)} < 1e-59.
        # The difference of each finite product from its limit is <= 2^{-239}.
        assert abs(normalization - 1) < Q('1e-59')
        print(f'q={q}, s={s:2d}, TV={tv:.9f}, optimal recovery={success:.9f}')


def check_unconditioned_block():
    # For source dimension 4, row count 2 and the standard symplectic
    # form, all 4x4 completed frames are precisely the symplectic group.
    # Enumerate all 2^16 pairs of top and bottom blocks.
    n = 4
    target = wedge(1, 2, 4) ^ wedge(4, 8, 4)
    rows = range(1 << n)
    completions = Counter()
    for x1 in rows:
        for x2 in rows:
            for y1 in rows:
                for y2 in rows:
                    if (wedge(x1, y1, n) ^ wedge(x2, y2, n)) == target:
                        completions[x1, x2] += 1
    assert sum(completions.values()) == 720
    for x1 in rows:
        for x2 in rows:
            kernel = [u for u in rows if not value(x1, u) and not value(x2, u)]
            j = len(kernel).bit_length()-1
            isotropic = all(not value(target, wedge(u, v, n))
                            for u, v in combinations(kernel, 2))
            expected = 2**(2*n-6+j*(j-1)//2) if isotropic else 0
            assert completions[x1, x2] == expected
    print('F2, n=4: verified all 256 unconditioned top-block masses, 720 completions')
    # Degrees for the Gaussian profile at fixed minimal kernel dimension 2.
    getcontext().prec = 80
    q = Q(2)
    e = [Q(1)]
    for h in range(1, 241):
        e.append(e[-1]*(1-q**(-h)))
    mass = [q**(-a*(a+2))*e[-1]/(e[a]*e[a+2]) for a in range(20)]
    cost = [(2+a)*(1+a)//2 for a in range(20)]
    mean = sum(p*c for p, c in zip(mass, cost))
    variance = sum(p*(c-mean)**2 for p, c in zip(mass, cost))
    print(f'q=r=2, unconditioned Gaussian window: mean={mean:.9f}, '
          f'sd={variance.sqrt():.9f}, center coefficient={1/mean:.9f}')


if __name__ == '__main__':
    check_small_planes()
    check_three_dimensional_planes()
    compute_table(2, range(-3, 4))
    check_unconditioned_block()
