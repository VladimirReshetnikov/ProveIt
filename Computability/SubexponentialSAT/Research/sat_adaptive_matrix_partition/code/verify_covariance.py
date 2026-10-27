#!/usr/bin/env python3
"""Exact 280-partition certificate for adaptive nine-group matrix summation.

No SAT/contraction runtime claim is inferred from these finite checks.  The
certificate verifies the finite combinatorial identities used in the uniform
mathematical proof.  It uses Python's standard library and integer arithmetic.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def triple_partitions(vertices: tuple[int, ...]):
    """Canonical unordered set partitions; each smallest vertex fixes a block."""
    if not vertices:
        yield ()
        return
    first, rest = vertices[0], vertices[1:]
    for pair in combinations(rest, 2):
        block = (first,) + pair
        remaining = tuple(v for v in rest if v not in pair)
        for tail in triple_partitions(remaining):
            yield (block,) + tail


def run() -> dict:
    edges = list(combinations(range(9), 2))
    partitions = list(triple_partitions(tuple(range(9))))
    require(len(edges) == 36, 'edge count')
    require(len(partitions) == 280, 'partition count')
    require(len(set(partitions)) == 280, 'duplicate partitions')
    classes = {(0, 1): 0, (0, 2): 1, (1, 2): 2}
    gram = [[0] * 36 for _ in edges]
    crossings = [0] * 36
    for partition in partitions:
        block_of = {v: i for i, block in enumerate(partition) for v in block}
        vectors = []
        class_counts = [0] * 3
        for e, (u, v) in enumerate(edges):
            a, b = sorted((block_of[u], block_of[v]))
            vec = [0, 0, 0]
            if a != b:
                cls = classes[a, b]
                vec = [-1, -1, -1]
                vec[cls] = 2
                class_counts[cls] += 1
                crossings[e] += 1
            vectors.append(vec)
        require(class_counts == [9, 9, 9], 'wrong interblock cardinalities')
        require([sum(v[j] for v in vectors) for j in range(3)] == [0, 0, 0],
                'centered edge vectors do not sum to zero')
        for e in range(36):
            for f in range(36):
                gram[e][f] += sum(vectors[e][j] * vectors[f][j] for j in range(3))
    require(crossings == [210] * 36, 'crossing probability is not 3/4')

    # The vectors above are three times the centered vectors in the proof.
    denominator = 9 * len(partitions)
    expected = {2: Fraction(1, 2), 1: Fraction(1, 28), 0: Fraction(-1, 21)}
    category_counts = {2: 0, 1: 0, 0: 0}
    a = [[0] * 36 for _ in edges]
    for e, edge in enumerate(edges):
        for f, other in enumerate(edges):
            overlap = len(set(edge).intersection(other))
            category_counts[overlap] += 1
            require(Fraction(gram[e][f], denominator) == expected[overlap],
                    f'covariance mismatch at {edge}, {other}')
            a[e][f] = {2: 21, 1: -3, 0: 1}[overlap]
            pe = Fraction(int(e == f), 1) - Fraction(1, 36)
            # M <= (27/28) P_e, because the difference is (7/12) Q,
            # Q = A/28 is an orthogonal projector checked below.
            require(Fraction(27, 28) * pe - expected[overlap]
                    == Fraction(a[e][f], 48), 'projector decomposition')

    require(all(sum(row) == 0 for row in a), 'projector does not kill constants')
    require(sum(a[e][e] for e in range(36)) == 28 * 27, 'projector rank')
    for e in range(36):
        for f in range(36):
            require(a[e][f] == a[f][e], 'projector not symmetric')
            require(sum(a[e][k] * a[k][f] for k in range(36)) == 28 * a[e][f],
                    f'projector not idempotent at {e}, {f}')

    # Exact scalar algebra connecting covariance to the new exponent bound.
    centered_variance = Fraction(27, 28)
    deviation_square = Fraction(3, 5) ** 2 * Fraction(2, 3) * centered_variance
    require(deviation_square == Fraction(81, 350), 'deviation coefficient')
    mean_square = Fraction(18, 5) ** 2
    triangle_square = (mean_square + deviation_square) * Fraction(2, 81)
    require(triangle_square == Fraction(57, 175), 'triangle coefficient')
    pair_merge_square = Fraction(14 + 2 + 14, 81) - Fraction(21 * 2, 25 * 81)
    triple_merge_square = Fraction(12 + 4 + 24, 81) - Fraction(21 * 4, 25 * 81)
    require(pair_merge_square == Fraction(708, 2025), 'pair merge coefficient')
    require(triple_merge_square == Fraction(916, 2025), 'triple merge coefficient')
    require(triangle_square < pair_merge_square < triple_merge_square,
            'wrong local bottleneck')
    require(Fraction(4, 9) < triple_merge_square,
            'largest table exponent does not fit within work bound')
    return {
        'status': 'passed',
        'partitions': 280,
        'unordered_edges': 36,
        'directed_edges': 72,
        'crossing_count_per_edge': 210,
        'interblock_counts_per_partition': [9, 9, 9],
        'covariance_checks': 1296,
        'covariance_by_overlap': {str(k): str(v) for k, v in expected.items()},
        'covariance_category_counts': {str(k): v for k, v in category_counts.items()},
        'psd_certificate': {
            'matrix': 'Q = A/28, A_ef = 21 (same), -3 (adjacent), 1 (disjoint)',
            'symmetric': True,
            'identity': 'A*A = 28*A',
            'rank': 27,
            'covariance_difference': '(27/28)*(I-J/36) - M = A/48 = (7/12)*Q',
            'checked_matrix_entries': 1296,
        },
        'squared_local_coefficients': {
            'adaptive_triangle': str(triangle_square),
            'pair_merge': str(pair_merge_square),
            'triple_merge': str(triple_merge_square),
            'largest_stored_table': '4/9',
        },
        'scope': 'Exact finite identities for the new mathematical lemma; no full SAT solver or fast matrix backend is implemented here.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered, end='')
