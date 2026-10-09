"""Deterministic exhaustive and randomized audit, with exact executed counters."""
from pathlib import Path
from math import comb
import json
import platform
import random
import time
from disc_basis import Candidate, reduce_family, exterior_feature, grade, star_partition, top_pairing, cut_feature
from check_certificate import verify
from reference import partitions, compatible, minor_feature, gf2_rank, best_cost, graph_data, ribbon_boundaries, forest_join, mobius_homogeneous

ROOT = Path(__file__).resolve().parents[1]


def exterior_product(x, y):
    """Literal exterior multiplication of bitset coefficient vectors over F_2."""
    answer = 0
    while x:
        a = x & -x
        i = a.bit_length()-1
        z = y
        while z:
            b = z & -z
            j = b.bit_length()-1
            if not i & j:
                answer ^= 1 << (i | j)
            z ^= b
        x ^= a
    return answer


def main():
    started = time.perf_counter()
    rng = random.Random(2026100909)
    rows, pair_checks, minor_checks, weighted_checks, certificates = [], 0, 0, 0, 0
    for r in range(1, 7):
        ps = list(partitions(r))
        matrix = []
        for p in ps:
            assert exterior_feature(p) == minor_feature(p)
            minor_checks += 1
            row = 0
            for j, q in enumerate(ps):
                good = compatible(p, q)
                assert top_pairing(p, q) == good
                assert bool(exterior_product(exterior_feature(p), exterior_feature(q))) == (graph_data(p, q)['cycle_rank'] == 0)
                pair_checks += 1
                row |= int(good) << j
            matrix.append(row)
        rank = gf2_rank(matrix)
        assert rank == 1 << (r-1)
        grade_ranks = []
        for d in range(r):
            subrank = gf2_rank([row for p, row in zip(ps, matrix) if grade(p) == d])
            assert subrank == comb(r-1, d)
            grade_ranks.append(subrank)
        for trial in range(12):
            # Some full, some incomplete families, with signed weights and ties.
            chosen = ps if trial < 3 else rng.sample(ps, rng.randrange(len(ps)+1))
            cs = [Candidate(f'{i}', p, rng.randrange(-1000, 1001)) for i, p in enumerate(chosen)]
            kept, out = reduce_family(cs, r)
            assert verify([c.record() for c in cs], out['certificate'])
            certificates += 1
            cut, _ = reduce_family(cs, r, method='cut', certificate=False)
            for q in ps:
                expected = best_cost(cs, q)
                assert best_cost(kept, q) == expected
                assert best_cost(cut, q) == expected
                weighted_checks += 1
        cs = [Candidate(str(i), p, rng.randrange(-1000, 1001)) for i, p in enumerate(ps)]
        ext, _ = reduce_family(cs, r, certificate=False)
        cut, _ = reduce_family(cs, r, method='cut', certificate=False)
        rows.append({'r': r, 'partitions': len(ps), 'disc_matrix_rank': rank,
                     'grade_ranks': grade_ranks, 'exterior_kept': len(ext), 'cut_kept': len(cut)})
    # Further independent minor checks at width seven.
    for p in partitions(7):
        assert exterior_feature(p) == minor_feature(p)
        minor_checks += 1
    cut_rank_table = []
    mobius_checks = 0
    for r in range(1, 9):
        ps = list(partitions(r))
        features = [(p, cut_feature(p)) for p in ps]
        cut_ranks = []
        for d in range(r):
            rank = gf2_rank([row for p, row in features if grade(p) == d])
            expected = 1 if d == r-1 else sum(comb(r-1, i) for i in range(d+1))
            assert rank == expected
            cut_ranks.append(rank)
        for p, row in features:
            assert mobius_homogeneous(row, r, grade(p)) == exterior_feature(p)
            mobius_checks += 1
        cut_rank_table.append({'r': r, 'grade_ranks': cut_ranks, 'total': sum(cut_ranks)})
    ribbon_checks = 0
    for _ in range(2000):
        r = rng.randrange(1, 9)
        def random_part():
            raw = [rng.randrange(r) for _ in range(r)]
            canon = {}
            return tuple(canon.setdefault(x, len(canon)) for x in raw)
        p, q = random_part(), random_part()
        orders = []
        for part in (p, q):
            side = [[i for i, b in enumerate(part) if b == j] for j in range(max(part)+1)]
            for b in side: rng.shuffle(b)
            orders.append(side)
        boundary = ribbon_boundaries(*orders)
        g = graph_data(p, q)
        chi = g['vertices']-g['edges']
        genus_twice = 2*g['components']-boundary-chi
        assert genus_twice >= 0 and genus_twice % 2 == 0
        assert compatible(p, q) == (g['components'] == 1 and boundary == 1 and genus_twice == 0)
        ribbon_checks += 1
    # Optimal-size negative control, with exactly one possible completion per row.
    hard = []
    for r in range(1, 11):
        cs = [Candidate(str(a), star_partition(r, a), a) for a in range(1 << (r-1))]
        kept, _ = reduce_family(cs, r, certificate=False)
        assert len(kept) == len(cs)
        hard.append({'r': r, 'kept': len(kept)})
    composition_queries = 0
    for trial in range(40):
        r = 4
        ps = list(partitions(r))
        full = [Candidate(str(i), p, rng.randrange(20)) for i, p in enumerate(rng.sample(ps, 9))]
        small, _ = reduce_family(full, r, certificate=False)
        for stage in range(3):
            patches = [(p, rng.randrange(-4, 5)) for p in rng.sample(ps, 4)]
            def apply(cs):
                result = []
                for i, c in enumerate(cs):
                    for j, (q, w) in enumerate(patches):
                        part = forest_join(c.partition, q)
                        if part is not None:
                            result.append(Candidate(f'{i}_{j}', part, c.cost+w))
                return result
            full = apply(full)
            small, _ = reduce_family(apply(small), r, certificate=False)
            for q in ps:
                assert best_cost(full, q) == best_cost(small, q)
                composition_queries += 1
    result = {'seed': 2026100909, 'python': platform.python_version(), 'platform': platform.platform(),
              'partition_pair_checks': pair_checks, 'incidence_minor_checks': minor_checks,
              'weighted_completion_queries': weighted_checks, 'independent_certificates': certificates,
              'ribbon_surface_checks': ribbon_checks, 'mobius_projection_checks': mobius_checks, 'cut_rank_table': cut_rank_table, 'staged_join_queries': composition_queries,
              'rank_table': rows, 'optimal_family': hard, 'seconds': time.perf_counter()-started,
              'scope': 'abstract finite partitions, ribbon thickenings, and algebraic joins; no native knot execution'}
    (ROOT/'results'/'audit.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
