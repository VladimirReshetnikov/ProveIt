#!/usr/bin/env python3
"""Check supplied independent exhaustive data without rerunning C++ enumeration.

The TSV files are precomputed results. This mandatory Python check validates
normalizations, complete row totals, and exact low-k/marked-transform agreement.
Use reproduce.py --optional-cpp to independently regenerate the TSVs themselves.
"""
from collections import defaultdict
import csv
from fractions import Fraction as F
from math import factorial, comb
from pathlib import Path
import json
from check_fixed_permanent import kernel_poly, expand_kernel, formulas


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def generate(optional):
    counts = {}
    with (optional/'audit_counts.tsv').open(newline='') as stream:
        rows = csv.DictReader(stream, delimiter='\t')
        require(rows.fieldnames == ['mode', 'n', 'k', 'count'], 'count table header')
        for row in rows:
            key = row['mode'], int(row['n']), int(row['k'])
            value = int(row['count'])
            require(key not in counts and value > 0 and key[0] in ('all_binary', 'diagonal_one', 'strong')
                    and 1 <= key[1] <= 5 and 0 <= key[2] <= factorial(key[1]), 'invalid count table row')
            counts[key] = value
    for n in range(1, 6):
        require(sum(v for (mode, m, k), v in counts.items() if (mode, m) == ('all_binary', n)) == 2**(n*n), 'full binary row total')
        require(sum(v for (mode, m, k), v in counts.items() if (mode, m) == ('diagonal_one', n)) == 2**(n*(n-1)), 'diagonal-one row total')
        for k in range(1, factorial(n)+1):
            require(k*counts.get(('all_binary', n, k), 0) == factorial(n)*counts.get(('diagonal_one', n, k), 0), 'marked matching identity')
            require(counts.get(('strong', n, k), 0) <= counts.get(('diagonal_one', n, k), 0), 'SCC subset')
    N = 6
    kernels, unused = kernel_poly(4)
    S = {2: [F(0), F(0)]+[F(1, n) for n in range(2, N)]}
    S.update({k: expand_kernel(v, N) for k, v in kernels.items()})
    D = formulas(S, N, 4)
    for n in range(1, N):
        for k in range(1, 5):
            require(D[k][n]*factorial(n)*2**comb(n, 2) == counts.get(('diagonal_one', n, k), 0), 'exact low-k graph counts')
            if k > 1:
                require(S[k][n]*factorial(n) == counts.get(('strong', n, k), 0), 'exact low-k SCC counts')
    # Multiset-marked transform, independent of the unmarked formulas routine.
    unit = (1, ())
    def multiply(a, b):
        result = defaultdict(F)
        for (k, marks), v in a.items():
            for (ell, other), w in b.items():
                if k*ell <= 4:
                    result[k*ell, tuple(sorted(marks+other))] += v*w
        return result
    V = [defaultdict(F) for unused in range(N)]
    for k, series in S.items():
        for n, v in enumerate(series):
            if v:
                V[n][k, ((k, n),)] = v
    W = [defaultdict(F) for unused in range(N)]
    W[0][unit] = 1
    for n in range(N):
        for key, v in V[n].items():
            W[n][key] -= v
        for m in range(n+1):
            for key, v in multiply(V[m], V[n-m]).items():
                W[n][key] += v/2
    B = [defaultdict(F) for unused in range(N)]
    for n in range(N):
        for m in range(n+1):
            for key, v in W[m].items():
                B[n][key] += v*F((-1)**(n-m), factorial(n-m)*2**comb(n, 2))
    marked = [defaultdict(F) for unused in range(N)]
    marked[0][unit] = 1
    for n in range(1, N):
        for m in range(1, n+1):
            for key, v in multiply(B[m], marked[n-m]).items():
                marked[n][key] -= v
    wanted = {}
    with (optional/'audit_block_counts.tsv').open(newline='') as stream:
        rows = csv.DictReader(stream, delimiter='\t')
        require(rows.fieldnames == ['n', 'k', 'marks', 'count'], 'block table header')
        for row in rows:
            marks = tuple(tuple(map(int, p.split(':'))) for p in row['marks'].split(';') if p)
            key = int(row['n']), int(row['k']), marks
            value = int(row['count'])
            require(key not in wanted and value > 0 and 1 <= key[0] <= 5 and 1 <= key[1] <= 4
                    and marks == tuple(sorted(marks)), 'invalid block table row')
            wanted[key] = value
    got = {(n, k, marks): v*factorial(n)*2**comb(n, 2)
           for n in range(1, N) for (k, marks), v in marked[n].items() if v}
    require(got == wanted, 'exact marked SCC transform')
    return {'status': 'PASS', 'exhaustive_data_mode': 'precomputed TSV data checked; C++ not invoked here',
            'count_table_rows': len(counts), 'marked_table_rows': len(wanted),
            'all_binary_maximum_n': 5, 'diagonal_one_maximum_n': 5,
            'low_k_transform_maximum_k': 4,
            'matching_invariance_exhaustive_maximum_n_if_Cpp_rerun': 4}


if __name__ == '__main__':
    result = generate(Path(__file__).resolve().parent.parent/'optional')
    with open('precomputed_audit_checks.json', 'x', encoding='utf-8') as stream:
        json.dump(result, stream, sort_keys=True, indent=2)
        stream.write('\n')
    print('PASS: supplied independent exhaustive data agrees with exact transforms')
