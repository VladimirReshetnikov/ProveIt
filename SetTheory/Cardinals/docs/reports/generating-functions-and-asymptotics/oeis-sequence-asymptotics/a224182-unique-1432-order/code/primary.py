#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True
"""Exact word-based construction and finite certificate. No local imports."""
from itertools import permutations, combinations
from collections import Counter
from fractions import Fraction
import hashlib, json, math


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def standardize(word):
    ranks = {x: i + 1 for i, x in enumerate(sorted(word))}
    require(len(ranks) == len(word), 'standardization requires distinct values')
    return tuple(ranks[x] for x in word)


def occurrences(p):
    found = []
    for j in range(1, len(p) - 2):
        for k in range(j + 1, len(p) - 1):
            if p[j] <= p[k]:
                continue
            for l in range(k + 1, len(p)):
                if p[k] > p[l]:
                    found.extend((i, j, k, l) for i in range(j) if p[i] < p[l])
    return found


def split(p, core):
    i, j, k, l = core
    a, b, c, d = (p[t] for t in core)
    require(a < d < c < b, 'not a 1432 core')
    q = [3 * x for x in p]
    q[j], q[l] = 3 * c - 1, 3 * c + 1
    q = q[:k] + [3 * d, q[k], 3 * b] + q[k + 1:]
    return standardize(q), k + 1


def unsplit(q, K):
    require(0 < K < len(q) - 1, 'center has no two neighbors')
    C, D, B = q[K], q[K - 1], q[K + 1]
    require(1 < C < len(q) and D < C < B, 'invalid center values')
    j, l = q.index(C - 1), q.index(C + 1)
    require(j < K - 1 and l > K + 1, 'adjacent values in invalid positions')
    w = list(q)
    w[j], w[l] = B, D
    return standardize([v for t, v in enumerate(w) if t not in (K - 1, K + 1)])


def minima(p):
    return tuple((i, v) for i, v in enumerate(p) if all(w > v for w in p[:i]))


def increasing4(p):
    return any(p[i] < p[j] < p[k] < p[l] for i, j, k, l in combinations(range(len(p)), 4))


def regions(p, core):
    i, j, k, l = core
    a, b, c, d = (p[t] for t in core)
    return (sum(x < d for x in p[:j]) == 1
            and sum(x > c for x in p[i + 1:k]) == 1
            and sum(d < x < b for x in p[j + 1:l]) == 1
            and sum(a < x < c for x in p[k + 1:]) == 1)


def inflate(p, i):
    a = p[i]
    w = tuple(x + (3 if x > a else 0) for x in p)
    return w[:i] + (a, a + 3, a + 2, a + 1) + w[i + 1:]


def skeleton_digest(counts):
    payload = [[[list(point) for point in skeleton], number]
               for skeleton, number in sorted(counts.items())]
    raw = json.dumps(payload, separators=(',', ':'), ensure_ascii=True).encode('ascii')
    return hashlib.sha256(raw).hexdigest()


def run():
    by_size = []
    inverse_certificate = []
    obstruction_records = []
    pattern_counter_checks = 0
    for n in range(4, 9):
        count = 0
        images = set()
        left, right = Counter(), Counter()
        candidate_count = 0
        for p in permutations(range(1, n + 1)):
            hits = occurrences(p)
            if n <= 6:
                independent = [c for c in combinations(range(n), 4)
                               if standardize(tuple(p[t] for t in c)) == (1, 4, 3, 2)]
                require(sorted(hits) == independent, ('pattern counter', p))
                pattern_counter_checks += 1
            sk = minima(p)
            if not hits:
                left[sk] += 1
            if not increasing4(p):
                right[sk] += 1
            if len(hits) == 1:
                count += 1
                core = hits[0]
                require(regions(p, core), ('necessary regions', p))
                q, K = split(p, core)
                require(not occurrences(q), ('split avoidance', p, core))
                require(unsplit(q, K) == p, ('marked inverse', p, q, K))
                require((q, K) not in images, ('marked collision', p))
                images.add((q, K))
            elif len(hits) > 1:
                for core in sorted(hits):
                    if regions(p, core):
                        candidate_count += 1
                        bad_split = split(p, core)[0]
                        split_hits = sorted(occurrences(bad_split))
                        require(bool(split_hits), ('image certificate', p, core))
                        obstruction_records.append({'n': n, 'source': list(p), 'core': list(core),
                                                    'split': list(bad_split), 'witness': list(split_hits[0])})
        require(left == right, ('fixed minima skeletons', n))
        dist = Counter()
        for sk, number in left.items():
            dist[len(sk)] += number
        by_size.append({'n': n, 'permutations': math.factorial(n), 'unique1432': count,
                        'marked_images': len(images), 'avoiders': sum(left.values()),
                        'fixed_minima_skeletons': len(left), 'skeleton_sha256': skeleton_digest(left),
                        'minima_distribution': [dist[r] for r in range(1, n + 1)]})
        inverse_certificate.append({'n': n, 'multiple_cores_passing_regions': candidate_count,
                                    'splits_still_containing1432': candidate_count})
    inflation_count = 0
    inflated_images = set()
    for n in range(1, 6):
        for p in permutations(range(1, n + 1)):
            if occurrences(p):
                continue
            for i, _ in minima(p):
                q = inflate(p, i)
                require(occurrences(q) == [(i, i + 1, i + 2, i + 3)], ('inflation', p, i))
                require(q not in inflated_images, ('inflation collision', p, i))
                inflated_images.add(q)
                inflation_count += 1
    sources = [(3, 5, 4, 6, 8, 1, 9, 7, 2), (3, 8, 5, 1, 4, 2, 6, 9, 7)]
    require(all(len(occurrences(p)) == 1 for p in sources), 'collision sources not unique')
    q, K = split(sources[0], occurrences(sources[0])[0])
    s, L = split(sources[1], occurrences(sources[1])[0])
    require(q == s and K != L, 'unmarked collision missing')
    threshold = (2, 1, 1, 1, 1, 1)
    up = down = 0
    for p in permutations(range(1, 7)):
        if any(p[i] < threshold[i] for i in range(6)):
            continue
        inc = sum(p[i] < p[j] < p[k] for i, j, k in combinations(range(6), 3))
        dec = sum(p[i] > p[j] > p[k] >= threshold[i] for i, j, k in combinations(range(6), 3))
        up += inc == 1
        down += dec == 1
    example = (1, 3, 6, 2, 4, 7, 5)
    require(not occurrences(example), 'sole-support input not an avoider')
    bad = unsplit(example, 4)
    require(bad == (1, 5, 4, 3, 2) and len(occurrences(bad)) == 4, 'sole-support example')
    quotient = 9 ** 2 * 3 * 9 ** 3
    remaining, exponent = quotient, 0
    while remaining > 1 and remaining % 3 == 0:
        remaining //= 3
        exponent += 1
    require(remaining == 1, 'constant quotient is not an exact power of three')
    return {'obstruction_records': obstruction_records, 'by_size': by_size, 'inverse_certificate': inverse_certificate,
            'pattern_counter_checks': pattern_counter_checks, 'inflation_cases': inflation_count,
            'collision': {'sources': [list(p) for p in sources], 'image': list(q), 'zero_based_marks': [K, L]},
            'board': {'thresholds': list(threshold), 'one123': up, 'one321': down},
            'sole_support': {'avoider': list(example), 'zero_based_mark': 4, 'source': list(bad), 'occurrences': 4},
            'constants': {'lower_ratio': str(Fraction(1, 3 * 9 ** 3)), 'upper_ratio': str(Fraction(9 ** 2)),
                          'constant_quotient': str(Fraction(quotient)),
                          'unrounded_width': str(Fraction(exponent, 2))}}
