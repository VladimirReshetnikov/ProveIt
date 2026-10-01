#!/usr/bin/env python3
"""Independent checks of the repository example and the new small witnesses.

The 30-vertex edge list is transcribed from ProveIt at commit
0744012ba29db0e345c44be953c6de3e000439e6, file
SetTheory/Cardinals/docs/reports/graph-theory/
domination-root-minus-four-order-30/domination_root_30.tex, equation (2.1).
This script checks its alternating evaluation, NOT its root at -4; the latter
is the original report's polynomial certificate.
"""
from pathlib import Path
import json
from verify import (adjacency, brute_polynomial, evaluate, feedback_evaluation,
                    spanning_forest)

REPO_EDGES = [(0,1),(1,2),(2,3),(3,0),(1,4),(2,4),(4,5),(4,6),(4,7),
              (4,8),(4,9),(1,10),(10,11),(2,12),(12,13),(12,14),(14,15),
              (15,16),(14,17),(17,18),(14,19),(19,20),(14,21),(21,22),
              (21,23),(21,24),(3,25),(25,26),(25,27),(27,28),(28,29)]
H5_EDGES = [(0,3),(0,5),(0,1),(0,2),(1,2),(1,6),(2,7),(3,4),(4,5),(6,7)]


def subcubic_extremizer(b: int):
    if b < 1:
        raise ValueError('b must be positive')
    edges = [(4*j+i, 4*j+(i+1)%4) for j in range(b) for i in range(4)]
    n = 4*b
    for j in range(b-1):
        z, leaf = n, n+1
        n += 2
        edges += [(4*j+2,z), (z,4*(j+1)), (z,leaf)]
    return n, edges


def main():
    value, counts = feedback_evaluation(30, REPO_EDGES)
    assert value == -3 and counts[-1] == 3 and counts[0] == 6 and counts[1] == 0
    assert len(spanning_forest(30, REPO_EDGES)[1]) == 2
    coeffs = brute_polynomial(8, H5_EDGES)
    assert evaluate(coeffs, -1) == 5 and evaluate(coeffs, -6) != 0
    assert len(spanning_forest(8, H5_EDGES)[1]) == 3
    sharp = []
    for b in range(1, 7):
        n, edges = subcubic_extremizer(b)
        assert max(map(len, adjacency(n, edges))) <= 3
        assert len(spanning_forest(n, edges)[1]) == b
        actual = feedback_evaluation(n, edges)[0]
        assert actual == (-1)**(b-1)*3**b
        sharp.append({'beta': b, 'vertices': n, 'edges': len(edges), 'value': actual})
    report = {'status': 'PASS',
              'repo_commit': '0744012ba29db0e345c44be953c6de3e000439e6',
              'repo_example': {'vertices': 30, 'edges': 31, 'beta': 2, 'D_minus_one': value,
                               'feedback_case_counts': dict(counts)},
              'H5': {'vertices': 8, 'edges': H5_EDGES,
                     'polynomial_coefficients_ascending': coeffs,
                     'D_minus_one': 5, 'D_minus_six': evaluate(coeffs,-6)},
              'subcubic_equality_examples': sharp}
    out = Path(__file__).resolve().parents[1] / 'results' / 'example_checks.json'
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
