"""Reproducible finite audits; run from the package root with -m."""
import itertools
import json
import platform
import random
import time
from pathlib import Path
from dualforest import (from_dense, solve, solve_pair, verify_positive,
                        verify_pair_optimality, verify_negative)
from dualforest.dependencies import build, peel, reach
from dualforest.intersection import transversal
from .oracles import tree_oracle, defect_oracle, transversal_oracle, full_positive_oracle

OUT = Path(__file__).resolve().parents[1] / 'results'


def check(inst, counter):
    expected = tree_oracle(inst)['yes']
    result = solve(inst, try_incumbent=False)
    assert result['status'] != 'unknown'
    assert (result['status'] == 'yes') == expected, (inst.data(), result)
    if expected:
        assert verify_positive(inst, result['certificate'])
        counter['yes'] += 1
    else:
        if 'optimality' in result:
            assert verify_pair_optimality(inst, result['optimality'])
        else:
            assert verify_negative(inst, result['negative_certificate'])
        counter['no'] += 1
    counter['instances'] += 1
    counter['branches'] += result['stats']['branches']
    counter['max_branches'] = max(counter['max_branches'], result['stats']['branches'])


def run():
    start = time.perf_counter()
    records = {}
    def stage(name, iterable):
        counter = dict(instances=0, yes=0, no=0, branches=0, max_branches=0)
        t = time.perf_counter()
        for inst in iterable:
            check(inst, counter)
        counter['seconds'] = time.perf_counter() - t
        records[name] = counter
        print(name, counter, flush=True)

    def small_graphs():
        edge_types = [(0, 0), (0, 1), (1, 1)]
        for edges in itertools.product(edge_types, repeat=3):
            if (0, 1) not in edges:
                continue
            for values in itertools.product(range(3), repeat=6):
                yield from_dense(2, edges, [values[0:2], values[2:4], values[4:6]])
    stage('exhaustive_three_rows_two_columns_all_rooted_two_vertex_multigraphs', small_graphs())

    def ternary_square():
        for values in itertools.product(range(3), repeat=9):
            yield from_dense(2, [(0, 1), (0, 1), (1, 1)],
                             [values[0:3], values[3:6], values[6:9]])
    stage('exhaustive_ternary_three_by_three_fixed_loop_graph', ternary_square())

    rng = random.Random(20261012)
    def mixed():
        for _ in range(2000):
            v = rng.randint(1, 5)
            m = rng.randint(max(4, v - 1), 10)
            n = rng.randint(1, 12)
            edges = [(i - 1, i) for i in range(1, v)]
            edges += [(rng.randrange(v), rng.randrange(v)) for _ in range(m - len(edges))]
            matrix = [[0] * n for _ in range(m)]
            for c in range(n):
                pool = list(range(4)) if rng.randrange(3) == 0 else list(range(m))
                size = rng.randint(0, 4) if len(pool) == 4 else rng.randint(0, 2)
                for r in rng.sample(pool, size):
                    matrix[r][c] = rng.randint(1, 2)
            yield from_dense(v, edges, matrix)
    stage('random_mixed_up_to_ten_rows_exceptional_boundary_at_most_four', mixed())

    def full_five():
        for _ in range(150):
            v = rng.randint(1, 4)
            edges = [(i - 1, i) for i in range(1, v)]
            edges += [(rng.randrange(v), rng.randrange(v)) for _ in range(5 - len(edges))]
            yield from_dense(v, edges, [[rng.randrange(3) for _ in range(5)] for _ in range(5)])
    stage('random_five_by_five_unrestricted', full_five())

    t = time.perf_counter()
    for _ in range(1000):
        v = rng.randint(1, 5)
        edges = [(i - 1, i) for i in range(1, v)]
        edges += [(rng.randrange(v), rng.randrange(v)) for _ in range(rng.randrange(5))]
        inst = from_dense(v, edges, [[] for _ in edges])
        groups = [{r for r in range(inst.m) if rng.randrange(3)}
                  for _ in range(rng.randrange(7))]
        ans = transversal(inst, groups)
        assert ans['size'] == transversal_oracle(inst, groups)
    records['independent_transversal_assignment_comparisons'] = dict(instances=1000, seconds=time.perf_counter()-t)

    t = time.perf_counter()
    total_seed_sets = 0
    for _ in range(500):
        v = rng.randint(1, 4)
        m = rng.randint(max(v - 1, 1), 7)
        edges = [(i - 1, i) for i in range(1, v)]
        edges += [(rng.randrange(v), rng.randrange(v)) for _ in range(m - len(edges))]
        matrix = [[0] * 6 for _ in range(m)]
        for c in range(6):
            for r in rng.sample(range(m), rng.randint(0, min(2, m))):
                matrix[r][c] = rng.randint(1, 2)
        inst = from_dense(v, edges, matrix)
        ans = solve_pair(inst)
        assert ans['optimality']['defect'] == defect_oracle(inst)
        assert verify_pair_optimality(inst, ans['optimality'])
        info = build(inst)
        for mask in range(1 << m):
            seed = {r for r in range(m) if mask >> r & 1}
            lhs = peel(inst, seed) is not None
            rhs = len(reach(info['adj'], info['anchors'] | seed)) == m
            assert lhs == rhs
            total_seed_sets += 1
    records['pair_optimal_defect_and_all_seed_sets'] = dict(instances=500, seed_sets=total_seed_sets,
                                                           seconds=time.perf_counter()-t)

    t = time.perf_counter()
    for values in itertools.product(range(3), repeat=9):
        matrix = tuple(tuple(values[3*r:3*r+3]) for r in range(3))
        inst = from_dense(1, [(0, 0)]*3, matrix)
        assert (peel(inst, []) is not None) == full_positive_oracle(matrix)
    records['inherited_peeling_vs_all_positive_pivot_orders'] = dict(instances=3**9,
                                                                    seconds=time.perf_counter()-t)
    result = dict(seed=20261012, python=platform.python_version(), platform=platform.platform(),
                  total_seconds=time.perf_counter()-start, stages=records,
                  mismatches=0,
                  scope='Matrix/graph kernels only. Native topology and full recognizer not run.')
    OUT.mkdir(exist_ok=True)
    (OUT/'validation.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    run()
