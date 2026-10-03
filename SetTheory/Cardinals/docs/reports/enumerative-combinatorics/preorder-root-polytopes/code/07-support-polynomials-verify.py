"""Deterministic finite checks accompanying the written proofs.

Default: all 4x4 bipartite graphs, all 3x4 graphs, all labelled preorders
through size 4, and seeded weighted examples. Standard library only.
These are finite regression tests, not a proof of any universal theorem.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
import random
import time
from support_tools import BipartiteGraph, bits, ulc, polynomial_value, down_up_sample, uniform_mixing_steps


def demands(g: BipartiteGraph) -> dict[int, int]:
    """Exact receiver-support counts via Hall inequalities, not matchings."""
    neighbours = [0] * (1 << g.n)
    t = g.transpose()
    for s in range(1, 1 << g.n):
        bit = s & -s
        neighbours[s] = neighbours[s ^ bit] | t.rows[bit.bit_length() - 1]
    result: dict[int, int] = {}
    def compositions(remaining: int, length: int):
        if length == 0:
            yield ()
        else:
            for a in range(remaining + 1):
                for tail in compositions(remaining - a, length - 1):
                    yield (a,) + tail
    for c in compositions(g.m, g.n):
        if all(sum(c[j] for j in bits(s)) <= neighbours[s].bit_count()
               for s in range(1, 1 << g.n)):
            supp = sum(1 << j for j, a in enumerate(c) if a)
            result[supp] = result.get(supp, 0) + 1
    return result


def support_counts(g: BipartiteGraph):
    states = g.supports()
    c = [0] * (min(g.m, g.n) + 1)
    by_y: dict[int, int] = {}
    for a, b in states:
        c[a.bit_count()] += 1
        by_y[b] = by_y.get(b, 0) + 1
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    return states, c, by_y


def preorder_coefficients(rows: tuple[int, ...]) -> list[int]:
    n = len(rows)
    ideals = [s for s in range(1 << n)
              if all(not (rows[i] & s) or bool(s >> i & 1) for i in range(n))]
    # rows[i] contains successors of i; ideal contains every predecessor.
    out = [0] * (n + 1)
    def vectors(rem: int, length: int):
        if length == 0:
            yield ()
        else:
            for a in range(rem + 1):
                for tail in vectors(rem - a, length - 1):
                    yield (a,) + tail
    for v in vectors(n, n):
        if all(sum(v[i] for i in bits(s)) <= s.bit_count() for s in ideals):
            out[sum(x > 0 for x in v)] += 1
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('../data/verification.json'))
    parser.add_argument('--quick', action='store_true', help='Only a 3x3 exhaustive graph test.')
    args = parser.parse_args()
    start = time.monotonic()
    report = {'seed': 20260929, 'status': 'PASS', 'scope': 'finite exact checks; not formal proof'}
    graph_results = []
    sizes = [(3, 3)] if args.quick else [(4, 4), (3, 4)]
    for m, n in sizes:
        total_supports = palindromic_count = 0
        for encoding in range(1 << (m * n)):
            rows = tuple((encoding >> (n * i)) & ((1 << n) - 1) for i in range(m))
            g = BipartiteGraph(rows, n)
            states, c, by_y = support_counts(g)
            assert ulc(c, min(m, n)), (rows, c)
            core = g.active_core()
            assert ulc(c, min(core.m, core.n))
            pal = c == c[::-1]
            assert pal == g.palindromic_core_test(), (rows, c)
            palindromic_count += pal
            r = len(c) - 1
            top = [(a, b) for a, b in states if a.bit_count() == r]
            assert len(top) == len({a for a, b in top}) * len({b for a, b in top})
            assert c[-1] >= (core.m - r + 1) * (core.n - r + 1)
            # Independent basis oracle, distinct from matching-support DP.
            oracle_bases = set()
            for base in combinations(range(m + n), m):
                if g.is_basis(base):
                    oracle_bases.add((sum(1 << i for i in range(m) if i not in base),
                                      sum(1 << (e - m) for e in base if e >= m)))
            assert states == oracle_bases
            if m <= 3:
                assert by_y == demands(g), (rows, by_y, demands(g))
            total_supports += len(states)
        graph_results.append({'m': m, 'n': n, 'graphs': 1 << (m * n),
                              'supports_checked': total_supports,
                              'palindromic_graphs': palindromic_count,
                              'receiver_refined_Hall_identity': m <= 3})
        print('Graph family passed:', graph_results[-1], flush=True)
    report['exhaustive_bipartite_graphs'] = graph_results

    preorder_results = []
    for n in range(5):
        offdiag = [(i, j) for i in range(n) for j in range(n) if i != j]
        count = 0
        for code in range(1 << len(offdiag)):
            rows = [1 << i for i in range(n)]
            for k, (i, j) in enumerate(offdiag):
                if code >> k & 1:
                    rows[i] |= 1 << j
            if not all(rows[j] & ~rows[i] == 0 for i, row in enumerate(rows) for j in bits(row)):
                continue
            g = BipartiteGraph(tuple(rows), n)
            c = [int(x) for x in g.coefficients()]
            assert c == preorder_coefficients(tuple(rows))
            assert c == c[::-1] and ulc(c, n)
            assert all(c[k] ** 2 > c[k-1] * c[k+1] for k in range(1, n))
            assert c[1] == sum(r.bit_count() for r in rows) if n else c == [1]
            count += 1
        preorder_results.append({'n': n, 'labelled_preorders': count})
    assert [r['labelled_preorders'] for r in preorder_results] == [1, 1, 4, 29, 355]
    report['exhaustive_preorders'] = preorder_results
    print('Preorders passed:', preorder_results, flush=True)

    rng = random.Random(20260929)
    for trial in range(300):
        m, n = rng.randrange(1, 6), rng.randrange(1, 6)
        rows = tuple(rng.randrange(1 << n) for _ in range(m))
        g = BipartiteGraph(rows, n)
        wx = [Fraction(rng.randrange(1, 8), rng.randrange(1, 6)) for _ in range(m)]
        wy = [Fraction(rng.randrange(1, 8), rng.randrange(1, 6)) for _ in range(n)]
        c = g.coefficients(wx, wy)
        core = g.active_core()
        d = min(core.m, core.n)
        assert ulc(c, d)
        for z in [Fraction(1, 3), Fraction(1), Fraction(7, 2)]:
            vals = [a * z ** k for k, a in enumerate(c)]
            Z = sum(vals)
            mu = sum(k*a for k,a in enumerate(vals)) / Z
            var = sum(k*k*a for k,a in enumerate(vals)) / Z - mu*mu
            if d:
                assert var <= mu * (1 - mu/d)
                if 0 < mu < d:
                    q = mu / d
                    binomlaw = [comb(d, k) * q ** k * (1 - q) ** (d-k) for k in range(d+1)]
                    # All convex-order stop-loss tests on the finite support.
                    for cut in range(d+1):
                        assert sum(max(k-cut,0)*a for k,a in enumerate(vals))/Z <= sum(max(k-cut,0)*a for k,a in enumerate(binomlaw))
                stars_equal = True
                small_g = g if core.m <= core.n else g.transpose()
                small_w, large_w = (wx,wy) if core.m <= core.n else (wy,wx)
                strengths = []
                used = 0
                for i,row in enumerate(small_g.rows):
                    if not row:
                        continue
                    if row & used:
                        stars_equal = False
                    used |= row
                    strengths.append(small_w[i] * sum(large_w[j] for j in bits(row)))
                stars_equal &= len(set(strengths)) <= 1
                assert (var == mu*(1-mu/d)) == stars_equal
            else:
                assert var == mu == 0
    report['weighted_rational_graphs'] = 300
    report['fugacities_per_weighted_graph'] = ['1/3', '1', '7/2']

    # Polynomial leaf formula checked at enough points to certify each identity.
    leaf_checks = 0
    for enc in range(16):
        g = BipartiteGraph((enc & 3, enc >> 2), 2)
        for ell in (1, 2):
            ext = g.leaf_extension(ell)
            lhs = ext.coefficients()
            base = g.coefficients()
            N = g.m + g.n
            # Expand the RHS directly with binomial coefficients.
            rhs = [Fraction(0)] * (N + 1)
            for k, a in enumerate(base):
                for j in range(N - 2*k + 1):
                    rhs[k+j] += a * comb(N-2*k, j) * ell**j
            while len(rhs)>1 and rhs[-1]==0:
                rhs.pop()
            assert lhs == rhs
            leaf_checks += 1
    report['leaf_identity_coefficient_checks'] = leaf_checks

    theta = BipartiteGraph((14,3,5,9),4)
    theta_c = [int(x) for x in theta.coefficients()]
    assert theta_c == [1,9,24,16,1]
    h = [0]*9
    for k,a in enumerate(theta_c):
        for j in range(8-2*k+1):
            h[k+j] += a*comb(8-2*k,j)
    assert h == [1,17,106,303,427,303,106,17,1]
    assert ulc(h,8)
    steps = uniform_mixing_steps(4,4,1e-8)
    samples = [down_up_sample(theta,steps,seed) for seed in range(30)]
    assert all(s in theta.supports() for s in samples)
    bad = BipartiteGraph((11,4,1),4)
    bad_c = [int(x) for x in bad.coefficients()]
    b = [Fraction(a,comb(3,k)*comb(4,k)) for k,a in enumerate(bad_c)]
    assert b[2]**2 < b[1]*b[3]
    report['examples'] = {'theta3_p': theta_c, 'theta3_height_two_h': h,
                          'theta3_h_total': sum(h), 'sampler_steps': steps,
                          'valid_sampler_runs':len(samples),
                          'false_two_sided_normalization_coefficients':bad_c,
                          'false_two_sided_normalization_normalized':[str(x) for x in b]}
    report['elapsed_seconds'] = round(time.monotonic()-start,3)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
