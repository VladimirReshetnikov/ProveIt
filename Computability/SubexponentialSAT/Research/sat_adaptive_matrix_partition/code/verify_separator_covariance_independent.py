#!/usr/bin/env python3
"""Independent exact covariance audit for adaptive r=16 streamed separators.

Derives the covariance by constructing leaf-path incidence columns directly
from least-common-ancestor binary intervals; it never enumerates all 16!
relabelings. Symmetry reduces the permutation average to three edge-pair types.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def verify():
    n = 16
    edges = list(combinations(range(n), 2))
    require(len(edges) == 120, 'edge count')
    incidence = []
    ycols = []
    for u, v in edges:
        # Minimal aligned dyadic interval containing both endpoint labels.
        block_size = 1 << (u ^ v).bit_length()
        block_index = u // block_size
        col = [int(leaf // block_size == block_index) for leaf in range(n)]
        require(sum(col) == block_size, 'LCA interval size')
        incidence.append(col)
        ycols.append([16 * x - block_size for x in col])
    require([sum(col[l] for col in incidence) for l in range(n)] == [85] * n,
            'leaf path does not contain exactly85 unordered cut pairs')
    require(all(sum(col) == 0 for col in ycols), 'uncentered leaf columns')
    require([sum(col[l] for col in ycols) for l in range(n)] == [0] * n,
            'constant edge weighting has positive leaf variance')

    categories = {2: [0, 0], 1: [0, 0], 0: [0, 0]}
    a = [[0] * 120 for _ in range(120)]
    expected = {2: F(19, 192), 1: F(5, 168), 0: F(-179, 17472)}
    for i, e in enumerate(edges):
        for j, f in enumerate(edges):
            overlap = len(set(e).intersection(f))
            categories[overlap][0] += sum(ycols[i][l] * ycols[j][l] for l in range(n))
            categories[overlap][1] += 1
            a[i][j] = {2: 182, 1: -13, 0: 2}[overlap]
    # (1/16) sum centered products, with centered columns multiplied by16,
    # followed by the average over the ordered edge-pair orbit.
    covariance = {k: F(s, 16**3 * count) for k, (s, count) in categories.items()}
    require(covariance == expected, 'averaged covariance values')
    diag, adjacent, disjoint = (covariance[k] for k in (2, 1, 0))
    eigen_trivial = diag + 28 * adjacent + 91 * disjoint
    eigen_standard = diag + 12 * adjacent - 13 * disjoint
    eigen_other = diag - 2 * adjacent + disjoint
    require(eigen_trivial == 0, 'constant eigenspace')
    require(eigen_standard == F(33, 56), 'standard eigenvalue')
    require(eigen_other == F(85, 2912), 'remaining eigenvalue')
    require(0 < eigen_other < eigen_standard, 'maximal eigenvalue')

    # Q=A/210 projects onto the104-dimensional remainder.  This turns the
    # spectral domination into an exact rational PSD certificate.
    for i, e in enumerate(edges):
        require(sum(a[i]) == 0, 'projector constant kernel')
        for j, f in enumerate(edges):
            overlap = len(set(e).intersection(f))
            pe = F(int(i == j), 1) - F(1, 120)
            require(eigen_standard * pe - covariance[overlap]
                    == (eigen_standard - eigen_other) * F(a[i][j], 210),
                    'PSD projector decomposition')
            require(a[i][j] == a[j][i], 'projector symmetry')
            require(sum(a[i][k] * a[k][j] for k in range(120)) == 210 * a[i][j],
                    'projector idempotence')
    require(sum(a[i][i] for i in range(120)) == 210 * 104, 'projector rank')

    mean = F(85, 120)
    require(mean == F(17, 24), 'mean path fraction')
    # max of16 numbers is at most mean + sqrt(15)*population-RMS deviation.
    beta_sq = (120 * mean**2 + 15 * eigen_standard) / 128
    require(beta_sq == F(725, 1344), 'new squared separator coefficient')
    old_beta_sq = F(170, 256)
    require(beta_sq < old_beta_sq, 'no strict improvement')
    require(beta_sq / old_beta_sq == F(290, 357), 'improvement ratio')
    return {
        'status': 'passed',
        'groups': 16,
        'unordered_edges': 120,
        'leaf_paths': 16,
        'undirected_pairs_per_leaf_path': 85,
        'directed_pairs_per_leaf_path': 170,
        'ordered_pair_orbit_sizes': {str(k): count for k, (_, count) in categories.items()},
        'ordered_covariance_entries_classified': 14400,
        'covariance_by_overlap': {str(k): str(v) for k, v in covariance.items()},
        'eigenvalues': {'constant': '0', 'standard_dimension15': str(eigen_standard),
                        'remainder_dimension104': str(eigen_other)},
        'psd_certificate': {
            'projector': 'Q=A/210, A entries182,-13,2 for same,adjacent,disjoint edges',
            'idempotence': 'A*A=210*A',
            'rank': 104,
            'covariance_difference': '(33/56)*(I-J/120)-M=(33/56-85/2912)*Q',
            'matrix_entries_checked': 14400,
        },
        'mean_path_fraction': str(mean),
        'maximum_to_population_rms_factor_squared': 15,
        'new_squared_local_coefficient': str(beta_sq),
        'old_squared_local_coefficient': str(old_beta_sq),
        'squared_new_to_old_ratio': '290/357',
        'scope': 'Finite exact combinatorial certificate for a polynomial-space summation refinement, not an implemented full contraction or SAT algorithm.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')
