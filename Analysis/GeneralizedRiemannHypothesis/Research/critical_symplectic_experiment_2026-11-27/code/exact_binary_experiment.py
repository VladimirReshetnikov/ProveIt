#!/usr/bin/env python3
"""Exact hidden-form experiment on F_2^4, including every observation sequence.

Dynamic programming on all row spans represents 35^t sequences without
sampling. Only the Python standard library is required.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
N = 4
D = 6
PAIRS = [(i, j) for i in range(N) for j in range(i+1, N)]


def add_row(basis, row):
    basis = list(basis)
    for pivot in basis:
        row = min(row, row ^ pivot)
    if not row:
        return tuple(basis)
    basis = [min(pivot, pivot ^ row) for pivot in basis]
    basis.append(row)
    return tuple(sorted(basis, reverse=True))


def wedge(u, v):
    out = 0
    for a, (i, j) in enumerate(PAIRS):
        bit = ((u >> i & 1)*(v >> j & 1)) ^ ((u >> j & 1)*(v >> i & 1))
        out |= bit << a
    return out


def matrix_rows(form):
    rows = [0]*N
    for a, (i, j) in enumerate(PAIRS):
        if form >> a & 1:
            rows[i] |= 1 << j
            rows[j] |= 1 << i
    return rows


def rank(rows):
    basis = ()
    for row in rows:
        basis = add_row(basis, row)
    return len(basis)


ROWS = tuple(sorted({wedge(u, v) for u in range(1, 16)
                     for v in range(1, 16) if u != v}))
GOOD = tuple(g for g in range(1, 64) if rank(matrix_rows(g)) == 4)
assert len(ROWS) == 35
assert len(GOOD) == 28


@lru_cache(None)
def candidates(basis):
    return tuple(g for g in GOOD if all((g & row).bit_count() % 2 == 0
                                       for row in basis))


@lru_cache(None)
def transition(basis):
    return tuple(Counter(add_row(basis, row) for row in ROWS).items())


def main():
    data = ROOT/'data'
    data.mkdir(exist_ok=True)
    distribution = {(): 1}
    reports = []
    histograms = {}
    for t in range(11):
        denom = 35**t
        mean = 28*Fraction(3, 7)**t
        assert sum(distribution.values()) == denom
        hist = Counter()
        q_dim = Counter()
        p_dim = Counter()
        full_tv = Fraction(0)
        recovery = unique = linear = Fraction(0)
        z_mean = Fraction(0)
        for basis, count in distribution.items():
            k, z = D-len(basis), len(candidates(basis))
            mass = Fraction(count, denom)
            hist[k, z] += count
            q_dim[k] += mass
            p_dim[k] += mass*z/mean
            z_mean += mass*z
            full_tv += mass*abs(Fraction(z)/mean-1)/2
            if z:
                recovery += mass/mean
            if z == 1:
                unique += mass/mean
            if k == 1:
                linear += mass*z/mean
        assert z_mean == mean
        assert sum(p_dim.values()) == 1
        dim_tv = sum(abs(q_dim[k]-p_dim[k]) for k in q_dim)/2
        assert full_tv >= dim_tv
        assert recovery >= unique >= linear
        if t >= D-1:
            zero_mass = sum(Fraction(count, denom) for (k,z),count in hist.items() if z==0)
            assert full_tv == zero_mass
            assert recovery == (1-full_tv)/mean
        reports.append({'t': t, 'a': t-(D-1), 'subspaces': len(distribution),
                        'sequences': str(denom), 'mean_Z': str(mean),
                        'full_tv': str(full_tv), 'dimension_tv': str(dim_tv),
                        'bayes_recovery': str(recovery), 'unique_recovery': str(unique),
                        'linear_recovery': str(linear)})
        histograms[str(t)] = [{'k':k, 'z':z, 'count':str(c)}
                              for (k,z),c in sorted(hist.items())]
        if t < 10:
            new = Counter()
            for basis, count in distribution.items():
                for dest, multiplicity in transition(basis):
                    new[dest] += count*multiplicity
            distribution = new
    # Verify the exact alternating count and tensor rank constraints separately.
    rank_counts = Counter(rank(matrix_rows(g)) for g in range(64))
    assert rank_counts == {0: 1, 2: 35, 4: 28}
    payload = {'model': 'Exact F_2^4 hidden alternating form experiment',
               'plane_count':len(ROWS), 'nondegenerate_form_count':len(GOOD),
               'alternating_rank_counts':dict(rank_counts),
               'checks':'integer enumeration, exact likelihood, means, normalization, optimal tests',
               'profiles':reports, 'joint_histograms':histograms}
    (data/'exact_binary_experiment.json').write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps({'verified': True, 't_values': len(reports),
                      'largest_sequence_space': str(35**10),
                      'largest_subspace_support': max(r['subspaces'] for r in reports),
                      'rank_counts': dict(rank_counts),
                      'critical_t5': reports[5]}, indent=2))


if __name__ == '__main__':
    main()
