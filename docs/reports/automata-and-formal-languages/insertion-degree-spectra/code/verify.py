#!/usr/bin/env python3
"""Exact checks for the insertion-spectrum constructions in article.tex.

Python 3.9+, standard library only.  No SMT solver is required.
Two independent methods are used: exhaustive assignment masks and a
minimum-cost dynamic program over the two source-word positions.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import random
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

Word = Tuple[int, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def words(alphabet: str, length: int) -> List[str]:
    return [''.join(x) for x in itertools.product(alphabet, repeat=length)]


def assignments(m: int, n: int) -> Iterable[Tuple[Tuple[int, ...], int]]:
    """Yield every source-position mask and its positive insertion degree."""
    if m < 0 or n < 0:
        raise ValueError('Lengths must be nonnegative.')
    for positions in itertools.combinations(range(m+n), m):
        chosen = set(positions)
        mask = tuple(int(i in chosen) for i in range(m+n))
        runs = sum(bit == 1 and (i == 0 or mask[i-1] == 0)
                   for i, bit in enumerate(mask))
        yield mask, max(1, runs)


def merge(u: str, v: str, mask: Sequence[int]) -> str:
    if sum(mask) != len(u) or len(mask)-sum(mask) != len(v):
        raise ValueError('Mask does not match source lengths.')
    i = j = 0
    out = []
    for bit in mask:
        if bit:
            out.append(u[i]); i += 1
        else:
            out.append(v[j]); j += 1
    return ''.join(out)


def pair_degrees(u: str, v: str) -> Dict[str, int]:
    result: Dict[str, int] = {}
    for mask, cost in assignments(len(u), len(v)):
        w = merge(u, v, mask)
        result[w] = min(result.get(w, cost), cost)
    return result


def dp_degree(u: str, v: str, w: str) -> Optional[int]:
    """Minimum number of A-runs, independently computed on an alignment DAG."""
    m, n = len(u), len(v)
    if len(w) != m+n:
        return None
    inf = m+n+2
    # Third coordinate: previous source was A (1) or B/start (0).
    dp = [[[inf, inf] for _ in range(n+1)] for _ in range(m+1)]
    dp[0][0][0] = 0
    for i in range(m+1):
        for j in range(n+1):
            if i+j == m+n:
                continue
            letter = w[i+j]
            for previous in (0, 1):
                cost = dp[i][j][previous]
                if cost == inf:
                    continue
                if i < m and u[i] == letter:
                    candidate = cost + (previous != 1)
                    dp[i+1][j][1] = min(dp[i+1][j][1], candidate)
                if j < n and v[j] == letter:
                    dp[i][j+1][0] = min(dp[i][j+1][0], cost)
    result = min(dp[m][n])
    return None if result == inf else max(1, result)


def language_degrees(A: Sequence[str], B: Sequence[str]) -> Dict[str, int]:
    result: Dict[str, int] = {}
    for u in A:
        for v in B:
            for w, cost in pair_degrees(u, v).items():
                result[w] = min(result.get(w, cost), cost)
    return result


def best_certificate(A: Sequence[str], B: Sequence[str], w: str) -> Tuple[int, str, str, str]:
    candidates = []
    for u in A:
        for v in B:
            for mask, cost in assignments(len(u), len(v)):
                if merge(u, v, mask) == w:
                    candidates.append((cost, u, v, ''.join('A' if x else 'B' for x in mask)))
    if not candidates:
        raise ValueError('Word is not a shuffle of these languages.')
    return min(candidates)


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    with path.open('w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(header)
        writer.writerows(rows)


def verify_finite(name: str, alphabet: str, A: List[str], B: List[str],
                  expected: Dict[int, int], out: Path) -> dict:
    degree_map = language_degrees(A, B)
    N = len(A[0])+len(B[0])
    universe = words(alphabet, N)
    pair_rows = []
    queries = 0
    three_words = set()
    for u in A:
        for v in B:
            brute = pair_degrees(u, v)
            for w in universe:
                require(dp_degree(u, v, w) == brute.get(w),
                        f'DP/mask mismatch: {u!r}, {v!r}, {w!r}')
                queries += 1
            spectrum = sorted(set(brute.values()))
            require(spectrum == list(range(1, max(spectrum)+1)),
                    f'Non-initial singleton spectrum: {u}, {v}')
            counts = Counter(brute.values())
            pair_rows.append([u, v, ' '.join(map(str, spectrum))] +
                             [counts.get(k, 0) for k in range(1, len(A[0])+1)])
            three_words.update(w for w, k in brute.items() if k == 3)
    require(dict(Counter(degree_map.values())) == expected, f'Wrong counts in {name}.')
    certificates = []
    for w in sorted(degree_map):
        k, u, v, mask = best_certificate(A, B, w)
        require(k == degree_map[w], 'Certificate is not optimal.')
        require(''.join(c for c, x in zip(w, mask) if x == 'A') == u, 'A projection failed.')
        require(''.join(c for c, x in zip(w, mask) if x == 'B') == v, 'B projection failed.')
        certificates.append([w, k, u, v, mask])
    write_csv(out / (name+'_degrees.csv'), ['word', 'degree', 'A_word', 'B_word', 'mask'], certificates)
    write_csv(out / (name+'_pairs.csv'), ['A_word', 'B_word', 'spectrum'] +
              ['count_degree_'+str(k) for k in range(1, len(A[0])+1)], pair_rows)
    if name == 'binary':
        erased = []
        for w in sorted(three_words):
            cert = best_certificate(A, B, w)
            require(cert[0] <= 2, 'A degree-three witness survived erasure.')
            erased.append([w, *cert])
        write_csv(out / 'binary_erasure.csv', ['word', 'degree', 'A_word', 'B_word', 'mask'], erased)
    return {'A': A, 'B': B, 'spectrum': sorted(expected),
            'degree_counts': expected, 'shuffle_words': len(degree_map),
            'source_pairs': len(A)*len(B), 'dp_queries': queries,
            'assignment_masks': len(A)*len(B)*sum(1 for _ in assignments(len(A[0]), len(B[0]))),
            'singleton_maximum_histogram': dict(Counter(int(row[2].split()[-1]) for row in pair_rows))}


def selected_positions(m: int, t: int) -> Tuple[int, ...]:
    if not (1 <= t <= m):
        raise ValueError('Need 1 <= t <= m.')
    # Zero-based form of J_{m,t} in the article.
    return tuple(range(m-t+1)) + tuple(m-t+2*j for j in range(1, t))


def construction(degrees: Sequence[int], m: Optional[int] = None):
    """Return alphabet size, N, exceptional words, and A membership predicate."""
    ts = tuple(degrees)
    if not ts or any(t < 2 for t in ts):
        raise ValueError('Supply a nonempty list of target degrees >= 2.')
    m = max(ts) if m is None else m
    if m < max(ts):
        raise ValueError('m is too small.')
    N = 2*m-1
    exceptions = {}
    targets = {}
    for block, t in enumerate(ts):
        w = tuple(block*N+j for j in range(N))
        u = tuple(w[j] for j in selected_positions(m, t))
        exceptions[u] = t
        targets[w] = t
    def in_A(u: Sequence[int]) -> bool:
        if len(u) != m:
            return False
        if tuple(u) in exceptions:
            return True
        return any(x//N != y//N or x >= y for x, y in zip(u, u[1:]))
    return len(ts)*N, m, N, targets, in_A


def predicate_degree(w: Word, m: int, in_A) -> Optional[int]:
    """Enumerate all possible A-position sets; B is the whole required length."""
    result = None
    for mask, cost in assignments(m, len(w)-m):
        u = tuple(a for a, bit in zip(w, mask) if bit)
        if in_A(u):
            result = cost if result is None else min(result, cost)
    return result


def verify_constructions() -> List[dict]:
    results = []
    for r in (2, 3):
        q, m, N, targets, in_A = construction([r])
        counts = Counter()
        for w in itertools.product(range(q), repeat=N):
            actual = predicate_degree(w, m, in_A)
            expected = targets.get(w, 1)
            require(actual == expected, f'Family mismatch r={r}, w={w}')
            counts[actual] += 1
        results.append({'target_degrees': [r], 'alphabet_size': q,
                        'tested_words': q**N, 'exhaustive': True,
                        'degree_counts': dict(counts)})
    rng = random.Random(20260920)
    for ts in ([4], [2, 4], [3, 5], [2, 3, 3, 4]):
        q, m, N, targets, in_A = construction(ts)
        samples = set(targets)
        for w in targets:
            # Exhaust every single-letter substitution in each target.
            for j in range(N):
                for a in range(q):
                    samples.add(w[:j]+(a,)+w[j+1:])
            for j in range(N-1):
                samples.add(w[:j]+(w[j+1], w[j])+w[j+2:])
        samples.update(tuple(rng.randrange(q) for _ in range(N)) for _ in range(1000))
        for w in samples:
            require(predicate_degree(w, m, in_A) == targets.get(w, 1),
                    f'Multiblock mismatch: {ts}, {w}')
        results.append({'target_degrees': list(ts), 'alphabet_size': q,
                        'tested_words': len(samples), 'exhaustive': False,
                        'random_seed': 20260920})
    return results


def verify_partition_types() -> dict:
    """All equality patterns of the five source positions (Bell number B_5=52)."""
    def rgs(prefix: Tuple[int, ...]):
        if len(prefix) == 5:
            yield prefix; return
        for k in range(max(prefix)+2):
            yield from rgs(prefix+(k,))
    count = 0
    histogram = Counter()
    for pattern in rgs((0,)):
        u = ''.join(chr(97+x) for x in pattern[:3])
        v = ''.join(chr(97+x) for x in pattern[3:])
        spectrum = sorted(set(pair_degrees(u, v).values()))
        require(spectrum == list(range(1, max(spectrum)+1)), 'Length-(3,2) singleton gap.')
        histogram[max(spectrum)] += 1
        count += 1
    require(count == 52, 'Equality-pattern enumeration is incomplete.')
    return {'patterns': count, 'maximum_histogram': dict(histogram)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parents[1]/'data')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    forbidden = {'aba', 'abb', 'abc', 'acb', 'bba', 'bca', 'bcb', 'cba'}
    ternary_A = [u for u in words('abc', 3) if u not in forbidden]
    report = {}
    report['ternary'] = verify_finite('ternary', 'abc', ternary_A, words('abc', 2),
                                     {1: 242, 3: 1}, args.out)
    report['binary'] = verify_finite('binary', 'ab',
        ['aaba', 'aabb', 'abbb', 'bbaa', 'bbba', 'bbbb'], ['aaa', 'aba', 'bab'],
        {1: 57, 2: 53, 4: 1}, args.out)
    report['families'] = verify_constructions()
    report['length_3_2_singletons'] = verify_partition_types()
    # Empty-word and empty-language boundary cases.
    require(pair_degrees('', '') == {'': 1}, 'Empty/empty case failed.')
    require(pair_degrees('', 'ab') == {'ab': 1}, 'Empty inserted word failed.')
    require(pair_degrees('ab', '') == {'ab': 1}, 'Empty target failed.')
    require(language_degrees([], ['a']) == {}, 'Empty-language case failed.')
    require(dp_degree('a', 'b', 'aa') is None, 'Nonmembership case failed.')
    report['status'] = 'PASS: all exact checks and all stated finite samples passed'
    (args.out/'verification.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
