#!/usr/bin/env python3
"""Exhaustive small checks of the local combinatorial lemmas and real functions.

The unrestricted proof is in the article. This script uses NumPy only for
truth-table tests. It does not enumerate the astronomical theorem seed.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import numpy as np
from labels import cyclic_edges, coherent, max_coherent_size, construct_labels
from profiles import Parameters, compute_profiles

ROOT = Path(__file__).resolve().parents[1]


def classify(heights, Q, q, k, r, edges, labels):
    g = Q - q
    T, G, accepts = [], [], []
    for i in range(k):
        target_failures = sum(heights[i * r + c] < Q for c in range(r))
        gate_failures = sum(heights[j * r + labels[i, j]] >= g
                            for u, j in edges if u == i)
        if target_failures == 0 and gate_failures == 0:
            accepts.append(i)
        elif target_failures == 1 and gate_failures == 0:
            T.append(i)
        elif target_failures == 0 and gate_failures == 1:
            G.append(i)
    return T, G, accepts


def geometry_checks():
    k, r = 3, 2
    edges = cyclic_edges(k)
    counts = dict(configurations=0, rejecting_configurations=0,
                  one_gate=0, two_gates=0, three_gates=0,
                  repaired_clause_transitions=0)
    for lab_tuple in itertools.product(range(r), repeat=len(edges)):
        labels = dict(zip(edges, lab_tuple))
        t = max_coherent_size(k, edges, labels) + 1
        assert t >= 4  # The cyclic triangle is always coherent.
        for Q in (2, 3):
            for heights in itertools.product(range(Q + 1), repeat=k*r):
                for q in range(1, Q):
                    T, G, accepts = classify(heights, Q, q, k, r, edges, labels)
                    counts['configurations'] += 1
                    if accepts:
                        continue
                    counts['rejecting_configurations'] += 1
                    assert coherent(T, edges, labels)
                    assert len(T) < t and len(G) <= 3
                    assert all((i, j) in edges for i in G for j in T)
                    out = {i: sum((i, j) in edges for j in G) for i in G}
                    assert all(v <= 1 for v in out.values())
                    if len(G) == 1:
                        counts['one_gate'] += 1
                    if len(G) == 2:
                        counts['two_gates'] += 1
                        source = next(i for i in G if out[i] == 1)
                        assert coherent(T + [source], edges, labels)
                        assert len(T) <= t - 2
                    if len(G) == 3:
                        counts['three_gates'] += 1
                        assert all(v == 1 for v in out.values())
                        assert coherent(T + G, edges, labels)
                        assert len(T) <= t - 4
                    # On all Q=2 states, examine every possible change of one
                    # child height. Raw bit changes are a subset of these.
                    if Q == 2:
                        candidates = set(T + G)
                        for index in range(k*r):
                            for value in range(Q + 1):
                                if value == heights[index]:
                                    continue
                                changed = list(heights)
                                changed[index] = value
                                _, _, after = classify(changed, Q, q, k, r, edges, labels)
                                if after:
                                    assert set(after) <= candidates
                                    counts['repaired_clause_transitions'] += 1
    assert counts['one_gate'] and counts['two_gates'] and counts['three_gates']
    return counts


def boolean_checks():
    # d=1, B=1, k=3, r=2 gives a genuine function on 18 raw bits.
    p = Parameters(depth=1, degree=1, positions=2, forbidden=4,
                   base_blocks=1, copies=1)
    bound = compute_profiles(p)[-1]
    edges = cyclic_edges(3)
    n = 18
    x = np.arange(1 << n, dtype=np.uint32)
    pc3 = np.array([i.bit_count() for i in range(8)], dtype=np.int8)
    heights = [np.maximum(pc3[(x >> (3*j)) & 7] - 1, 0) for j in range(6)]
    pc = np.zeros(1 << n, dtype=np.uint8)
    for bit in range(n):
        pc += ((x >> bit) & 1).astype(np.uint8)
    results = []
    for lab_tuple in itertools.product(range(2), repeat=3):
        labels = dict(zip(edges, lab_tuple))
        f = np.zeros(1 << n, dtype=bool)
        for i in range(3):
            clause = (heights[2*i] == 2) & (heights[2*i+1] == 2)
            for u, j in edges:
                if u == i:
                    clause &= heights[2*j + labels[i, j]] == 0
            f |= clause
        sensitivity = np.zeros(1 << n, dtype=np.uint8)
        for bit in range(n):
            sensitivity += f != f[x ^ (1 << bit)]
        s0 = int(sensitivity[~f].max())
        s1 = int(sensitivity[f].max())
        min_weight = int(pc[f].min())
        assert not f[0]
        assert s0 <= bound['s0'][1] and s1 <= bound['s1'][1]
        assert min_weight == 6
        assert all(f[((1 << 6) - 1) << (6*i)] for i in range(3))
        results.append(dict(labels=list(lab_tuple), s0=s0, s1=s1,
                            certified_s0=bound['s0'][1], certified_s1=bound['s1'][1],
                            exact_bs_at_zero=3, minimum_accepting_weight=min_weight))
    return dict(functions=len(results), inputs_per_function=1 << n,
                total_inputs=len(results)*(1 << n), bit_differences=len(results)*(1 << n)*n,
                cases=results)


def main():
    geometry = geometry_checks()
    truth = boolean_checks()
    labels, history = construct_labels(7, 2, 5)
    small = dict(rows=7, positions=2, forbidden=5,
                 labels=[dict(tail=i, head=j, label=c) for (i,j),c in labels.items()],
                 expectation_history=history,
                 max_coherent_size=max_coherent_size(7, cyclic_edges(7), labels),
                 scope="Small derandomization example, NOT the large seed labelling")
    (ROOT/'certificates'/'small_label_witness.json').write_text(json.dumps(small, indent=2)+'\n')
    report = dict(status='PASS', geometry=geometry, truth_tables=truth,
                  derandomization=dict(rows=7, maximum_coherent_size=small['max_coherent_size'],
                                       final_bad_sets=history[-1]), numpy_version=np.__version__)
    (ROOT/'results'/'local_checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({key: value for key,value in report.items() if key != 'truth_tables'},indent=2))
    print('Actual Boolean truth-table inputs checked:',truth['total_inputs'])
    print('Actual Boolean raw-bit differences checked:',truth['bit_differences'])

if __name__ == '__main__':
    main()
