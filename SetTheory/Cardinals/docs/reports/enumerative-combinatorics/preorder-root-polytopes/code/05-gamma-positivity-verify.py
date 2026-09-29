#!/usr/bin/env python3
"""Exact finite tests for Gamma-Positivity for Every Finite Preorder.

Python >=3.10, standard library only. Run from the package root:
    python code/verify.py --max-n 5 --out data
All mathematical computations use integers, exhaustive search and Boolean tests.
These finite tests are neither an all-size proof nor Lean verification.
"""
from __future__ import annotations
import argparse, csv, itertools, json, math, platform, random, sys, time
from pathlib import Path
from functools import lru_cache
from typing import Iterator


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def submasks(mask: int) -> Iterator[int]:
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub-1) & mask


def is_transitive(rows: tuple[int, ...]) -> bool:
    # rows[j] contains exactly the i for which i R j.
    return all(rows[i] & ~row == 0 for row in rows for i in bits(row))


def all_relations(n: int) -> Iterator[tuple[int, ...]]:
    full = (1 << n)-1
    options = [tuple(s | (1 << i) for s in submasks(full ^ (1 << i)))
               for i in range(n)]
    yield from itertools.product(*options)


def all_preorders(n: int) -> Iterator[tuple[int, ...]]:
    return (r for r in all_relations(n) if is_transitive(r))


def ideals(rows: tuple[int, ...]) -> list[int]:
    return [I for I in range(1 << len(rows))
            if all(rows[i] & ~I == 0 for i in bits(I))]


def matcher(rows: tuple[int, ...]):
    """Exact recursive matching test for arbitrary bipartite adjacency.

    Rows index the right shore, bits the left shore. No preorder property is
    assumed. Each pair of supports is counted once, regardless of witnesses.
    """
    @lru_cache(maxsize=None)
    def match(left: int, right: int) -> bool:
        if left.bit_count() != right.bit_count():
            return False
        if not right:
            return True
        j = min(bits(right), key=lambda v: (rows[v] & left).bit_count())
        return any(match(left ^ (1 << i), right ^ (1 << j))
                   for i in bits(rows[j] & left))
    return match


def compositions(n: int, cap: int) -> Iterator[tuple[int, ...]]:
    """All nonnegative n-tuples of total at most cap, without duplicates."""
    if n == 0:
        yield ()
        return
    for head in range(cap+1):
        for tail in compositions(n-1, cap-head):
            yield (head,) + tail


@lru_cache(maxsize=None)
def point_candidates(n: int) -> tuple[tuple[int, int], ...]:
    result = []
    for x in compositions(n, n):
        sums = [0]*(1 << n)
        bad = 0
        for I in range(1, 1 << n):
            bit = I & -I
            sums[I] = sums[I ^ bit] + x[bit.bit_length()-1]
            if sums[I] > I.bit_count():
                bad |= 1 << I
        support = sum(1 << i for i, v in enumerate(x) if v)
        result.append((support, bad))
    return tuple(result)


@lru_cache(maxsize=None)
def cores(n: int) -> tuple[tuple[int, int], ...]:
    full = (1 << n)-1
    return tuple((U, V) for U in range(1 << n) for V in submasks(full ^ U)
                 if U.bit_count() == V.bit_count())


def expand_gamma(g: list[int], n: int) -> list[int]:
    h = [0]*(n+1)
    for k, c in enumerate(g):
        for j in range(n-2*k+1):
            h[k+j] += c*math.comb(n-2*k, j)
    return h


def product_poly(a: list[int], b: list[int]) -> list[int]:
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def quotient(rows: tuple[int, ...]) -> tuple[tuple[int, ...], list[int]]:
    remaining = (1 << len(rows))-1
    blocks = []
    while remaining:
        i = next(bits(remaining))
        block = sum(1 << j for j in bits(remaining)
                    if rows[i] & (1 << j) and rows[j] & (1 << i))
        blocks.append(block)
        remaining ^= block
    qrows = tuple(sum(1 << i for i, b in enumerate(blocks)
                      if rows[next(bits(c))] & b) for c in blocks)
    return qrows, [b.bit_count() for b in blocks]


def gamma_blocks(rows: tuple[int, ...]) -> list[int]:
    qrows, sizes = quotient(rows)
    ids = ideals(qrows)
    g = [0]*(len(rows)//2+1)
    for d in itertools.product(*(range(-s, s+1) for s in sizes)):
        if sum(d) or any(sum(d[i] for i in bits(I)) < 0 for I in ids):
            continue
        shift = sum(max(0, v) for v in d)
        local = [1]
        for s, v in zip(sizes, d):
            r = abs(v)
            poly = [math.factorial(s)//(math.factorial(j)*math.factorial(j+r)
                    *math.factorial(s-r-2*j)) for j in range((s-r)//2+1)]
            local = product_poly(local, poly)
        for j, c in enumerate(local):
            g[shift+j] += c
    return g


def graph_matching_number(rows: tuple[int, ...]) -> int:
    n = len(rows)
    adj = [sum(1 << j for j in range(n) if i != j and
               (rows[i] & (1 << j) or rows[j] & (1 << i))) for i in range(n)]
    @lru_cache(maxsize=None)
    def size(mask: int) -> int:
        if not mask:
            return 0
        i = next(bits(mask))
        rest = mask ^ (1 << i)
        return max([size(rest)] + [1+size(rest ^ (1 << j)) for j in bits(rest & adj[i])])
    return size((1 << n)-1)


def check_preorder(rows: tuple[int, ...], doubled: bool = True) -> dict:
    n = len(rows)
    full = (1 << n)-1
    ids = ideals(rows)
    ideal_flag = sum(1 << I for I in ids)
    actual = [0]*(1 << n)
    for S, bad in point_candidates(n):
        if not bad & ideal_flag:
            actual[S] += 1
    h = [0]*(n+1)
    for S, c in enumerate(actual):
        h[S.bit_count()] += c
    match = matcher(rows)
    g = [0]*(n//2+1)
    expected = [0]*(1 << n)
    for U, V in cores(n):
        ok = match(U, V)
        hall = all((U & I).bit_count() >= (V & I).bit_count() for I in ids)
        assert ok == hall, ('ideal Hall', rows, U, V)
        if ok:
            g[U.bit_count()] += 1
            for W in submasks(full ^ (U | V)):
                expected[V | W] += 1
    assert actual == expected, ('multivariate support fibres', rows)
    assert expand_gamma(g, n) == h, ('gamma expansion', rows)
    assert gamma_blocks(rows) == g, ('block formula', rows)
    assert max(i for i, c in enumerate(g) if c) == graph_matching_number(rows)
    comparisons = 0
    if doubled:
        hp = [0]*(n+1)
        for A in range(1 << n):
            for B in range(1 << n):
                if A.bit_count() != B.bit_count():
                    continue
                comparisons += 1
                ok = match(A, B)
                assert ok == match(A & ~B, B & ~A), ('cancellation', rows, A, B)
                if ok:
                    hp[A.bit_count()] += 1
        assert hp == h, ('doubled graph', rows)
    poset = all(i == j or not(rows[i] & (1 << j) and rows[j] & (1 << i))
                for i in range(n) for j in range(n))
    for k, c in enumerate(g):
        assert c <= math.factorial(n)//(math.factorial(k)**2*math.factorial(n-2*k))
        if poset:
            assert c <= math.comb(n, 2*k)*math.comb(2*k, k)//(k+1)
    return {'n': n, 'principal_ideals': list(rows), 'h': h, 'gamma': g,
            'lattice_points': sum(h), 'support_fibres': 1 << n,
            'cancellation_comparisons': comparisons}


def check_demands(max_shore: int = 3) -> dict:
    graphs = demand_count = 0
    for p in range(max_shore+1):
        for q in range(max_shore+1):
            for rows in itertools.product(range(1 << p), repeat=q):
                graphs += 1
                neighborhoods = [0]*(1 << q)
                for T in range(1, 1 << q):
                    bit = T & -T
                    neighborhoods[T] = neighborhoods[T ^ bit] | rows[bit.bit_length()-1]
                demand_fibres = [0]*(1 << q)
                for c in compositions(q, p):
                    if all(sum(c[j] for j in bits(T)) <= neighborhoods[T].bit_count()
                           for T in range(1 << q)):
                        S = sum(1 << j for j, value in enumerate(c) if value)
                        demand_fibres[S] += 1
                match = matcher(rows)
                matching_fibres = [sum(match(U, V) for U in range(1 << p)
                                       if U.bit_count() == V.bit_count())
                                   for V in range(1 << q)]
                assert demand_fibres == matching_fibres, ('support-resolved demand identity', p, q, rows)
                demand_count += sum(demand_fibres)
    return {'graphs': graphs, 'total_feasible_demands': demand_count,
            'largest_shores': [max_shore, max_shore]}


def check_cancellation_characterization(max_n: int = 4) -> dict:
    counts = []
    for n in range(max_n+1):
        total = transitive = 0
        for rows in all_relations(n):
            total += 1
            tr = is_transitive(rows)
            transitive += tr
            match = matcher(rows)
            cancel = True
            for A in range(1 << n):
                for B in range(1 << n):
                    if A.bit_count() == B.bit_count() and \
                            match(A, B) != match(A & ~B, B & ~A):
                        cancel = False
                        break
                if not cancel:
                    break
            assert tr == cancel, ('transitivity characterization', rows)
            polynomial = [0]*(n+1)
            for A in range(1 << n):
                for B in range(1 << n):
                    if A.bit_count() == B.bit_count() and match(A, B):
                        polynomial[A.bit_count()] += 1
            assert (polynomial == polynomial[::-1]) == tr, ('palindromicity', rows)
            if n:
                assert polynomial[1] == sum(r.bit_count() for r in rows)
                assert polynomial[n-1] == sum(r.bit_count() for r in closure(list(rows)))
                assert (polynomial[1] == polynomial[n-1]) == tr
            if tr:
                gamma = [sum(match(U, V) for U, V in cores(n) if U.bit_count() == k)
                         for k in range(n//2+1)]
                assert expand_gamma(gamma, n) == polynomial
        counts.append({'n': n, 'reflexive_relations': total, 'with_cancellation': transitive})
    bad = (1, 3, 6)  # 0 R 1, 1 R 2, but not 0 R 2; every loop is present.
    match = matcher(bad)
    pbad = [sum(match(A, B) for A in range(8) for B in range(8)
                if A.bit_count() == B.bit_count() == k) for k in range(4)]
    assert pbad == [1, 5, 6, 1]
    return {'counts': counts, 'nontransitive_example': list(bad), 'p': pbad}


def closure(rows: list[int]) -> tuple[int, ...]:
    n = len(rows)
    for i in range(n):
        rows[i] |= 1 << i
    for k in range(n):
        for j in range(n):
            if rows[j] & (1 << k):
                rows[j] |= rows[k]
    return tuple(rows)


def sampled_preorders(seed: int = 20260929) -> list[tuple[int, ...]]:
    rng = random.Random(seed)
    result = set()
    for n in (6, 7, 8):
        for _ in range(24):
            density = rng.choice((0.08, 0.18, 0.35))
            result.add(closure([sum(1 << i for i in range(n) if rng.random() < density)
                                for j in range(n)]))
        for _ in range(24):
            order = list(range(n))
            rng.shuffle(order)
            rows = [1 << i for i in range(n)]
            for i in range(n):
                for j in range(i+1, n):
                    if rng.random() < 0.4:
                        rows[order[j]] |= 1 << order[i]
            result.add(closure(rows))
    return sorted(result, key=lambda r: (len(r), r))


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O: this verifier uses assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=5, choices=range(6))
    parser.add_argument('--out', type=Path, default=Path('data'))
    parser.add_argument('--skip-samples', action='store_true')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    report = {'python': sys.version, 'platform': platform.platform(),
              'scope': 'finite exact tests; not proof-assistant verification',
              'seed': 20260929, 'preorders_by_size': []}
    report['bipartite_demand_identity'] = check_demands()
    print('Bipartite demand identity:', report['bipartite_demand_identity'], flush=True)
    report['cancellation_characterization'] = check_cancellation_characterization()
    print('Cancellation characterization: passed', flush=True)
    with (args.out/'preorders.csv').open('w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['n', 'principal_ideal_bitmasks', 'h_coefficients', 'gamma_coefficients'])
        for n in range(args.max_n+1):
            tick = time.perf_counter()
            count = fibres = comparisons = points = 0
            for rows in all_preorders(n):
                value = check_preorder(rows)
                count += 1
                fibres += value['support_fibres']
                comparisons += value['cancellation_comparisons']
                points += value['lattice_points']
                writer.writerow([n, ';'.join(map(str, rows)), ';'.join(map(str, value['h'])),
                                 ';'.join(map(str, value['gamma']))])
            assert count == [1, 1, 4, 29, 355, 6942][n]
            row = {'n': n, 'preorders': count, 'support_fibres': fibres,
                   'equal_size_support_pairs': comparisons, 'lattice_points_counted': points,
                   'seconds': round(time.perf_counter()-tick, 3)}
            report['preorders_by_size'].append(row)
            print(row, flush=True)
    samples = [] if args.skip_samples else sampled_preorders()
    report['larger_samples'] = [check_preorder(rows, doubled=False) for rows in samples]
    for n in range(21):
        universal = tuple([(1 << n)-1]*n)
        expected = [math.factorial(n)//(math.factorial(k)**2*math.factorial(n-2*k))
                    for k in range(n//2+1)]
        assert gamma_blocks(universal) == expected
        assert expand_gamma(expected, n) == [math.comb(n, j)**2 for j in range(n+1)]
        chain_gamma = [math.comb(n, 2*k)*math.comb(2*k, k)//(k+1) for k in range(n//2+1)]
        assert expand_gamma(chain_gamma, n) == [math.comb(n+1, j)*math.comb(n+1, j+1)//(n+1)
                                               for j in range(n+1)]
    report['elementary_families_through_n'] = 20
    report['total_exhaustive_preorders'] = sum(r['preorders'] for r in report['preorders_by_size'])
    report['total_support_fibres'] = sum(r['support_fibres'] for r in report['preorders_by_size'])
    report['sample_count'] = len(samples)
    report['total_seconds'] = round(time.perf_counter()-start, 3)
    report['all_checks_passed'] = True
    (args.out/'verification.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print('All checks passed:', report['total_exhaustive_preorders'], 'exhaustive preorders;',
          len(samples), 'larger samples;', report['total_seconds'], 'seconds.', flush=True)


if __name__ == '__main__':
    main()
