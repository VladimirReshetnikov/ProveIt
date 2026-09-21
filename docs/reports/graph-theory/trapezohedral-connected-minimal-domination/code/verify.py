#!/usr/bin/env python3
"""Independent exact checks for the A381190 proof. Python standard library only.

The exhaustive verifier uses the literal definition: domination, failure of
all one-vertex deletions to dominate, and induced connectivity. It does not use
the structural classification or the private-neighbor lemma to filter sets.
"""
from __future__ import annotations

import argparse
from array import array
from collections import Counter
from collections.abc import Iterator
from decimal import Decimal, ROUND_FLOOR, localcontext
from fractions import Fraction
from math import comb
from pathlib import Path
import csv
import json
import platform
import time

ROOT = Path(__file__).resolve().parents[1]


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def graph(n: int) -> list[int]:
    """a_i=2*i, b_i=2*i+1, u=2*n, v=2*n+1, with i starting at 0."""
    if n < 3:
        raise ValueError('The n-trapezohedral graph is used only for n >= 3.')
    adj = [0] * (2 * n + 2)

    def edge(i: int, j: int) -> None:
        adj[i] |= 1 << j
        adj[j] |= 1 << i

    for i in range(n):
        edge(2 * i, 2 * i + 1)
        edge(2 * i + 1, 2 * ((i + 1) % n))
        edge(2 * n, 2 * i)
        edge(2 * n + 1, 2 * i + 1)
    assert sum(a.bit_count() for a in adj) == 8 * n
    return adj


def connected(mask: int, adj: list[int]) -> bool:
    if not mask:
        return False
    reached = frontier = mask & -mask
    while frontier:
        bit = frontier & -frontier
        frontier -= bit
        newly_reached = adj[bit.bit_length() - 1] & mask & ~reached
        reached |= newly_reached
        frontier |= newly_reached
    return reached == mask


def exhaustive_sets(n: int) -> set[int]:
    """Enumerate all 2^(2n+2) subsets, with no classification-based filtering."""
    adj = graph(n)
    total = 1 << len(adj)
    full = total - 1
    closed = [a | (1 << i) for i, a in enumerate(adj)]
    coverage = array('I', [0]) * total
    if coverage.itemsize < 4 or len(adj) > 32:
        raise ValueError('This exhaustive implementation needs 32-bit masks.')
    answer: set[int] = set()
    assert coverage[0] != full  # The empty subset is not dominating.
    for mask in range(1, total):
        first = mask & -mask
        coverage[mask] = coverage[mask ^ first] | closed[first.bit_length() - 1]
        if coverage[mask] != full:
            continue
        remaining = mask
        while remaining:
            bit = remaining & -remaining
            remaining -= bit
            if coverage[mask ^ bit] == full:
                break
        else:
            if connected(mask, adj):
                answer.add(mask)
    return answer


def classified_sets(n: int) -> set[int]:
    """Generate the cyclic-word classification, independently of enumeration."""
    answer: set[int] = set()
    for a_mask in range(1 << n):
        a = [(a_mask >> i) & 1 for i in range(n)]
        if any(not a[i] and not a[(i + 1) % n] for i in range(n)):
            continue
        if any(a[i - 1] and a[i] and a[(i + 1) % n] for i in range(n)):
            continue
        selected_a = sum(1 << (2 * i) for i in range(n) if a[i])
        for j in range(n):
            k = (j + 1) % n
            legal = (
                (a[j] and a[k])
                or (a[j] and not a[k] and not a[j - 1])
                or (not a[j] and a[k] and not a[(k + 1) % n])
            )
            if not legal:
                continue
            rim = selected_a | (1 << (2 * j + 1))
            answer.add(rim | (1 << (2 * n)))
            # Rotation by one rim vertex swaps the poles and the a/b families.
            shifted = ((rim << 1) & ((1 << (2 * n)) - 1)) | (rim >> (2 * n - 1))
            answer.add(shifted | (1 << (2 * n + 1)))
    return answer


def choose(n: int, k: int) -> int:
    return comb(n, k) if n >= 0 and 0 <= k <= n else 0


def finite_sum(n: int) -> int:
    if n < 3:
        return 0
    subtotal = 0
    for s in range(n // 3 + 1):
        rest = n - 3 * s
        if rest % 2:
            continue
        r = rest // 2
        subtotal += 2 * choose(r + s - 1, s) + choose(r + s - 1, s - 1)
    return 2 * n * subtotal


def count_by_size(n: int) -> Counter[int]:
    counts: Counter[int] = Counter()
    for s in range(n // 3 + 1):
        rest = n - 3 * s
        if rest % 2:
            continue
        r = rest // 2
        d = 2 + r + 2 * s
        value = 2 * n * (2 * choose(r + s - 1, s) + choose(r + s - 1, s - 1))
        counts[d] += value
        rational_form = Fraction(2 * n * (2 * r + s) * comb(r + s, s), r + s)
        assert rational_form.denominator == 1 and rational_form == value
        assert r == 2 * n - 3 * d + 6 and s == 2 * d - n - 4
    return counts


def fast_terms(max_n: int) -> tuple[list[int], list[int]]:
    p = [0] * (max_n + 1)
    p[0] = 1
    for n in range(1, max_n + 1):
        p[n] = (p[n - 2] if n >= 2 else 0) + (p[n - 3] if n >= 3 else 0)
    a = [0] * (max_n + 1)
    for n in range(3, max_n + 1):
        a[n] = 2 * n * (2 * p[n - 2] + p[n - 3])
    return a, p


def gf_terms(max_n: int) -> list[int]:
    # Numerator and denominator of the OEIS conjecture, in ascending degree.
    numerator = [0, 0, 0, 6, 16, 18, -8, -16, -8]
    denominator = [1, 0, -2, -2, 1, 2, 1]
    a = [0] * (max_n + 1)
    for n in range(max_n + 1):
        a[n] = (numerator[n] if n < len(numerator) else 0) - sum(
            denominator[k] * a[n - k] for k in range(1, min(n, 6) + 1)
        )
    return a


def private_certificate(n: int, mask: int) -> dict[str, object]:
    """Return an auditable witness for every chosen vertex; not used for counting."""
    adj = graph(n)
    names = [f'{kind}{i + 1}' for i in range(n) for kind in ('a', 'b')] + ['u', 'v']
    cert = {}
    for v in bits(mask):
        candidates = [w for w in range(len(adj)) if ((adj[w] | (1 << w)) & mask) == 1 << v]
        if not candidates:
            raise AssertionError('No private neighbor exists.')
        cert[names[v]] = names[min(candidates)]
    return {'selected_vertices': [names[v] for v in bits(mask)], 'private_neighbors': cert}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--brute-max', type=int, default=10)
    parser.add_argument('--max-n', type=int, default=1000)
    args = parser.parse_args()
    if not 3 <= args.brute_max <= 11:
        parser.error('--brute-max must be in 3..11 (exhaustive exponential search).')
    if not 50 <= args.max_n <= 10000:
        parser.error('--max-n must be in 50..10000.')
    out = ROOT / 'data'
    out.mkdir(exist_ok=True)
    print('A381190 independent verification')
    print('Python:', platform.python_version())
    print('No external Python packages are required.')

    candidates = json.loads((out / 'candidates.json').read_text())
    selection = json.loads((out / 'selection.json').read_text())
    assert candidates[selection['zero_based_index']]['oeis'] == 'A381190'
    assert selection['one_based_index'] == 4 and selection['rerolls'] == 0
    print('Recorded RNG selection: candidate 4 / 4, A381190; no new random draw.')

    exhaustive_rows = []
    example_sets = None
    for n in range(3, args.brute_max + 1):
        started = time.perf_counter()
        direct = exhaustive_sets(n)
        structural = classified_sets(n)
        assert direct == structural, f'Exact set mismatch for n={n}'
        sizes = Counter(d.bit_count() for d in direct)
        assert sizes == count_by_size(n)
        assert len(direct) == finite_sum(n)
        row = {'n': n, 'vertices': 2 * n + 2, 'subsets_examined': 1 << (2 * n + 2),
               'count': len(direct), 'size_counts': dict(sorted(sizes.items()))}
        exhaustive_rows.append(row)
        print(f'n={n:2d}: {row["subsets_examined"]:9d} subsets; '
              f'{len(direct):4d} sets; exact classification and size distribution agree '
              f'({time.perf_counter() - started:.3f} s)')
        if n == 5:
            example_sets = direct
    (out / 'exhaustive_checks.json').write_text(json.dumps(exhaustive_rows, indent=2) + '\n')

    a, p = fast_terms(args.max_n)
    assert a == gf_terms(args.max_n)
    for n in range(3, args.max_n + 1):
        assert a[n] == finite_sum(n)
        assert a[n] == sum(count_by_size(n).values())
    for n in range(6, args.max_n + 1):
        assert (n - 2) * (n - 3) * a[n] == n * (n - 3) * a[n - 2] + n * (n - 2) * a[n - 3]
    for n in range(9, args.max_n + 1):
        assert a[n] == 2 * a[n - 2] + 2 * a[n - 3] - a[n - 4] - 2 * a[n - 5] - a[n - 6]
    print(f'GF division, finite sum, size refinement, and both recurrences agree through n={args.max_n}.')

    source_count = 0
    for line in (out / 'oeis_a381190_3_42.txt').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        n, value = map(int, line.split())
        assert a[n] == value
        source_count += 1
    assert source_count == 40
    print('All 40 OEIS values n=3..42 agree exactly.')

    with (out / 'terms.csv').open('w', newline='') as f:
        w = csv.writer(f); w.writerow(['n', 'a_n'])
        w.writerows((n, a[n]) for n in range(3, args.max_n + 1))
    with (out / 'size_distribution.csv').open('w', newline='') as f:
        w = csv.writer(f); w.writerow(['n', 'set_size', 'count'])
        for n in range(3, min(100, args.max_n) + 1):
            w.writerows((n, d, value) for d, value in sorted(count_by_size(n).items()))
    if example_sets is not None:
        certificates = [private_certificate(5, mask) for mask in sorted(example_sets)]
        (out / 'certificates_n5.json').write_text(json.dumps(certificates, indent=2) + '\n')

    # Exact rational checks underlying the uniform nearest-integer error bound.
    lower = Fraction(64, 49)
    assert lower ** 3 - lower - 1 < 0
    assert 360 * 7 ** 45 < 8 ** 45
    with localcontext() as ctx:
        ctx.prec = max(120, args.max_n // 5 + 100)
        lam = Decimal('1.3')
        for _ in range(30):
            lam -= (lam ** 3 - lam - 1) / (3 * lam * lam - 1)
        constant = 2 * (2 * lam + 1) / (2 * lam + 3)
        power = Decimal(1)
        asymptotic_rows = []
        for n in range(args.max_n + 1):
            if n:
                power *= lam
            main_term = constant * n * power
            if n >= 45:
                rounded = int((main_term + Decimal('0.5')).to_integral_value(rounding=ROUND_FLOOR))
                assert rounded == a[n], f'Nearest-integer check failed at n={n}'
            if n in (20, 45, 50, 100, 200, 500, 1000, args.max_n):
                asymptotic_rows.append({'n': n, 'exact': str(a[n]),
                                        'main_term': str(main_term),
                                        'error_exact_minus_main': str(Decimal(a[n]) - main_term)})
        constants = {'plastic_constant_lambda': str(lam), 'rho': str(1 / lam),
                     'leading_constant_C': str(constant), 'rows': asymptotic_rows}
        (out / 'asymptotics.json').write_text(json.dumps(constants, indent=2) + '\n')
        print(f'lambda = {lam:.40f}')
        print(f'C      = {constant:.40f}')
    print(f'Nearest-integer formula agrees for n=45..{args.max_n}; uniform bound proved separately in article.')
    print('PASS: all checks completed.')


if __name__ == '__main__':
    main()
