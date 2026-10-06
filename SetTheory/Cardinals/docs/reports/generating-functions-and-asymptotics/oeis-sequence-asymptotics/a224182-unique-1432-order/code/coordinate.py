#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True
"""Independent plot-based certificate, with direct four-index inequalities.
Does not import the word-based implementation or its results.
"""
from itertools import permutations, combinations
from collections import Counter
import hashlib, json, math


def check(ok, message):
    if not ok:
        raise RuntimeError(message)


def ranks(values):
    order = sorted(values)
    check(len(set(order)) == len(order), 'duplicate coordinate')
    return tuple(order.index(v) + 1 for v in values)


def occurrences(p):
    return [t for t in combinations(range(len(p)), 4)
            if p[t[0]] < p[t[3]] < p[t[2]] < p[t[1]]]


def points(p, core):
    i, j, k, l = core
    a, b, c, d = (p[t] for t in core)
    result = [(3 * t, 3 * v, t) for t, v in enumerate(p) if t != j and t != l]
    result.extend([(3 * j, 3 * c - 1, j), (3 * k - 1, 3 * d, l),
                   (3 * k + 1, 3 * b, j), (3 * l, 3 * c + 1, l)])
    return sorted(result)


def word(plot):
    return ranks([v for _, v, _ in plot])


def inverse(q, K):
    C, D, B = q[K], q[K - 1], q[K + 1]
    return ranks([B if v == C - 1 else D if v == C + 1 else v
                  for t, v in enumerate(q) if t != K - 1 and t != K + 1])


def region_test(p, core):
    i, j, k, l = core
    a, b, c, d = (p[t] for t in core)
    return ([(t, v) for t, v in enumerate(p) if t < j and v < d] == [(i, a)]
            and [(t, v) for t, v in enumerate(p) if i < t < k and v > c] == [(j, b)]
            and [(t, v) for t, v in enumerate(p) if j < t < l and d < v < b] == [(k, c)]
            and [(t, v) for t, v in enumerate(p) if t > k and a < v < c] == [(l, d)])


def digest(counts):
    rows = []
    for skeleton in sorted(counts):
        rows.append([[list(pt) for pt in skeleton], counts[skeleton]])
    return hashlib.sha256(json.dumps(rows, separators=(',', ':'), ensure_ascii=True).encode('ascii')).hexdigest()


def run():
    by_size, certificates = [], []
    obstruction_records = []
    commutations = 0
    for n in range(4, 9):
        unique = 0
        images = set()
        a1432, a1234 = Counter(), Counter()
        candidate_count = 0
        for p in permutations(range(1, n + 1)):
            hits = occurrences(p)
            skeleton = tuple((t, v) for t, v in enumerate(p) if min(p[:t + 1]) == v)
            if not hits:
                a1432[skeleton] += 1
            if not any(p[a] < p[b] < p[c] < p[d] for a, b, c, d in combinations(range(n), 4)):
                a1234[skeleton] += 1
            if len(hits) == 1:
                unique += 1
                core = hits[0]
                check(region_test(p, core), ('core regions', p))
                plot = points(p, core)
                q = word(plot)
                K = next(t for t, pt in enumerate(plot) if pt[:2] == (3 * core[2], 3 * p[core[2]]))
                check(not occurrences(q), ('coordinate avoidance', p, core))
                check(inverse(q, K) == p, ('coordinate inverse', p))
                check((q, K) not in images, ('coordinate collision', p))
                images.add((q, K))
                extras = [t for t in range(n) if t not in core]
                for r in range(len(extras) + 1):
                    for extra in combinations(extras, r):
                        S = sorted(core + extra)
                        reduced = ranks([p[t] for t in S])
                        reduced_core = tuple(S.index(t) for t in core)
                        check(word([pt for pt in plot if pt[2] in S]) == word(points(reduced, reduced_core)),
                              ('restriction commutation', p, core, S))
                        commutations += 1
            elif len(hits) > 1:
                for core in hits:
                    if region_test(p, core):
                        candidate_count += 1
                        bad_split = word(points(p, core))
                        split_hits = occurrences(bad_split)
                        check(bool(split_hits), ('inverse certificate', p, core))
                        obstruction_records.append({'n': n, 'source': list(p), 'core': list(core),
                                                    'split': list(bad_split), 'witness': list(split_hits[0])})
        check(a1432 == a1234, ('skeleton correspondence', n))
        dist = [sum(number for sk, number in a1432.items() if len(sk) == r) for r in range(1, n + 1)]
        by_size.append({'n': n, 'permutations': math.factorial(n), 'unique1432': unique,
                        'marked_images': len(images), 'avoiders': sum(a1432.values()),
                        'fixed_minima_skeletons': len(a1432), 'skeleton_sha256': digest(a1432),
                        'minima_distribution': dist})
        certificates.append({'n': n, 'multiple_cores_passing_regions': candidate_count,
                             'splits_still_containing1432': candidate_count})
    # Directly inspect every center of every small avoider; no counting-theorem shortcut.
    center_checks, eligible = 0, []
    for size in range(6, 9):
        accepted = set()
        for q in permutations(range(1, size + 1)):
            if occurrences(q):
                continue
            for K in range(1, size - 1):
                center_checks += 1
                C, D, B = q[K], q[K - 1], q[K + 1]
                if not (1 < C < size and D < C < B):
                    continue
                J, L = q.index(C - 1), q.index(C + 1)
                if not (J < K - 1 and L > K + 1):
                    continue
                p = inverse(q, K)
                j, k, l = J, K - 1, L - 2
                b, c, d = p[j], p[k], p[l]
                supporters = [i for i in range(j) if p[i] < d]
                if len(supporters) != 1:
                    continue
                core = (supporters[0], j, k, l)
                if not region_test(p, core):
                    continue
                check(occurrences(p) == [core], ('eligible-center false positive', q, K))
                check(word(points(p, core)) == q, ('candidate roundtrip', q, K))
                check(p not in accepted, ('eligible-center duplicate', p))
                accepted.add(p)
        expected = {p for p in permutations(range(1, size - 1)) if len(occurrences(p)) == 1}
        check(accepted == expected, ('eligible-center surjectivity', size))
        eligible.append({'output_size': size, 'eligible_centers': len(accepted)})
    return {'obstruction_records': obstruction_records, 'by_size': by_size, 'inverse_certificate': certificates,
            'restriction_commutations': commutations, 'small_avoider_center_checks': center_checks,
            'eligible_centers_by_size': eligible}
