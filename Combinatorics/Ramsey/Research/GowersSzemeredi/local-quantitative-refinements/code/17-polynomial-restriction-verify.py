#!/usr/bin/env python3
"""Finite audits for Polynomial-loss restriction in Gowers's argument.

Python 3.10+. Exact tests use only the standard library. Optional direct
phase averages use NumPy if present. These checks are not a proof of the
parametric theorems, and do not claim Lean verification.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import math
import random

SEED = 20261006

def fejer_signal(m: int, length: int) -> F:
    if m < 2 or length < 1:
        raise ValueError('m >= 2 and length >= 1 are required')
    return F(1) + 2 * sum((F(j, length) ** m for j in range(1, length)), F(0))

def rank_mod(rows: list[list[int]], p: int) -> int:
    if not rows:
        return 0
    a = [[v % p for v in row] for row in rows]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col], -1, p)
        a[rank] = [(v * inv) % p for v in a[rank]]
        for i in range(len(a)):
            if i != rank and a[i][col]:
                factor = a[i][col]
                a[i] = [(x - factor*y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank

def eps(m: int) -> tuple[int, ...]:
    return (1,) * (m//2) + (-1,) * (m//2)

def dot(a, b, p):
    return sum(x*y for x, y in zip(a, b)) % p

def bounded_relations(xs: tuple[int, ...], length: int, p: int):
    m = len(xs)
    for ns in product(range(1-length, length), repeat=m):
        if sum(ns) % p == 0 and dot(ns, xs, p) == 0:
            yield ns

def is_generic(xs: tuple[int, ...], length: int, p: int) -> bool:
    e = eps(len(xs))
    return all(all(n == ns[0]*s for n, s in zip(ns, e))
               for ns in bounded_relations(xs, length, p))

def exact_phase_product(xs: tuple[int, ...], ys: tuple[int, ...],
                        length: int, p: int) -> F:
    """Exact Fourier expansion of E_{u,v,c} prod_j K(u*x_j+v*y_j+c)."""
    answer = F(0)
    for ns in bounded_relations(xs, length, p):
        if dot(ns, ys, p) == 0:
            term = F(1)
            for n in ns:
                term *= F(length - abs(n), length**2)
            answer += term
    return answer

def moment_counts(graph: tuple[tuple[int, int], ...], p: int, order: int) -> int:
    sums: Counter[tuple[int, int]] = Counter({(0, 0): 1})
    for _ in range(order):
        nxt: Counter[tuple[int, int]] = Counter()
        for (x, y), n in sums.items():
            for a, b in graph:
                nxt[((x+a) % p, (y+b) % p)] += n
        sums = nxt
    return sum(n*n for n in sums.values())

def is_graph_coset(graph, p):
    if len(graph) == 1:
        return True
    if len(graph) != p:
        return False
    d = dict(graph)
    return any(all(d[x] == (a*x+b) % p for x in range(p))
               for a in range(p) for b in range(p))

def run():
    rng = random.Random(SEED)
    results: dict[str, object] = {'seed': SEED}
    checked = 0
    for m in (4, 6, 8, 10, 12, 16, 24, 32):
        for length in range(2, 129):
            signal = fejer_signal(m, length)
            assert signal >= F(2*length, m+1)
            assert signal <= length
            checked += 1
    results['exact_fejer_signal_checks'] = checked

    graph_tests = 0
    moment_tests = 0
    equality_tests = 0
    graphs = []
    for choices in product(range(-1, 3), repeat=3):
        graph = tuple((x, y) for x, y in enumerate(choices) if y >= 0)
        if graph:
            graphs.append((3, graph))
    for p in (5, 7):
        for _ in range(256):
            domain = [x for x in range(p) if rng.random() < .65]
            if not domain:
                domain = [rng.randrange(p)]
            graph = tuple((x, rng.randrange(p)) for x in domain)
            graphs.append((p, graph))
        # Include equality cases deliberately.
        for slope in range(p):
            graphs.append((p, tuple((x, (slope*x+2) % p) for x in range(p))))
    for p, graph in graphs:
        b = len(graph)
        e2 = moment_counts(graph, p, 2)
        for r in range(2, 9):
            er = moment_counts(graph, p, r)
            assert er * b**(r-2) >= e2**(r-1)
            if r > 2:
                equality = er * b**(r-2) == e2**(r-1)
                assert equality == is_graph_coset(graph, p)
                equality_tests += 1
            moment_tests += 1
        graph_tests += 1
    results.update(graphs_tested=graph_tests, exact_moment_inequalities=moment_tests,
                   exact_equality_classification_checks=equality_tests)

    p, length, m = 43, 3, 4
    examples = []
    attempts = 0
    while len(examples) < 24 and attempts < 10000:
        attempts += 1
        first = tuple(rng.randrange(p) for _ in range(m-1))
        last = sum(s*x for s, x in zip(eps(m)[:-1], first)) % p
        xs = first + (last,)
        if not is_generic(xs, length, p):
            continue
        assert len(set(xs)) == m
        good = tuple((3*x+5) % p for x in xs)
        bad = good[:-1] + ((good[-1]+1) % p,)
        base = F(1, length**m)
        assert exact_phase_product(xs, good, length, p) == base*fejer_signal(m, length)
        assert exact_phase_product(xs, bad, length, p) == base
        examples.append((xs, good, bad))
    assert len(examples) == 24
    results['exact_good_bad_survival_checks'] = 2*len(examples)

    try:
        import numpy as np
        vals = np.arange(p)
        kernel = np.abs(sum(np.exp(2j*np.pi*j*vals/p) for j in range(length)))**2/length**2
        uu, vv, cc = np.meshgrid(vals, vals, vals, indexing='ij')
        max_error = 0.0
        for xs, good, bad in examples[:8]:
            for ys in (good, bad):
                products = np.ones_like(uu, dtype=float)
                for x, y in zip(xs, ys):
                    products *= kernel[(uu*x+vv*y+cc) % p]
                direct = float(products.mean())
                exact = float(exact_phase_product(xs, ys, length, p))
                max_error = max(max_error, abs(direct-exact))
                assert abs(direct-exact) < 1e-12
        results['direct_phase_averages'] = 16
        results['direct_phase_max_abs_error'] = max_error
    except ImportError:
        results['direct_phase_averages'] = 'SKIPPED: NumPy unavailable'

    # All ordered additive quadruples in F_2^2: degenerate affine ranks.
    points = tuple(product(range(2), repeat=2))
    total = degenerate = 0
    for xs in product(points, repeat=4):
        if any(sum(x[j] for x in xs) % 2 for j in range(2)):
            continue
        total += 1
        matrix = [[x[j] for x in xs] for j in range(2)] + [[1]*4]
        if rank_mod(matrix, 2) < 3:
            degenerate += 1
    bound = ((2**2 - 1)//(2-1)) * len(points)**2
    assert degenerate <= bound
    results['F2_squared_degeneracy'] = {'tuples': total, 'degenerate': degenerate,
                                      'union_bound': bound}

    # Rank formula: arbitrary augmented column sets. Each test exhausts
    # every scalar linear functional on the augmented ambient space.
    rank_checks = 0
    rank_cases = []
    for p, ambient, count in ((2, 5, 48), (3, 4, 48)):
        for _ in range(count):
            mcols = rng.choice((4, 6))
            cols = [tuple(rng.randrange(p) for _ in range(ambient-1)) + (1,)
                    for _ in range(mcols)]
            matrix = [[col[i] for col in cols] for i in range(ambient)]
            rank = rank_mod(matrix, p)
            accepted = sum(all(dot(functional, col, p) == 0 for col in cols)
                           for functional in product(range(p), repeat=ambient))
            assert F(accepted, p**ambient) == F(1, p**rank)
            rank_checks += 1
            if len(rank_cases) < 4:
                rank_cases.append((p, ambient, cols, rank))
    results['exhaustive_linear_functional_rank_checks'] = rank_checks

    # Deliberately audit the repeated-point pitfall, not just the generic case.
    # For L=2 and p=7: E K = 1/2, whereas E K^4 = 35/128.
    xs = (0, 0, 0, 0)
    ys = (0, 0, 0, 0)
    assert exact_phase_product(xs, ys, 2, 7) == F(35, 128)
    assert F(1, 2) != F(35, 128)
    results['repeated_point_check'] = {'true_inclusion_probability': '1/2',
                                      'incorrect_product_value': '35/128'}

    table = []
    for alpha, eta in ((F(1,2), F(1,10)), (F(1,10), F(1,10)),
                       (F(1,100), F(1,100))):
        m, beta = 16, F(1,2)
        length = math.ceil(F(m+1)/(alpha*eta))
        new_log = -math.log10(2*float(eta))-m*math.log10(length)
        old_log = (2**19)*math.log10(float(alpha*eta/4))
        threshold_log = (math.log10(2)+m*math.log10(length)
                         +(m-1)*math.log10(2*length-1)
                         -(m-1)*math.log10(float(beta)))
        table.append({'alpha': str(alpha), 'eta': str(eta), 'beta': str(beta),
                      'L': length, 'log10_old_retention': old_log,
                      'log10_new_retention': new_log,
                      'log10_sufficient_N_threshold': threshold_log})
    results['comparison_table'] = table
    results['status'] = 'PASS'
    results['scope_note'] = ('Finite exact and numerical audits only; the general proofs are in '
                             'article.tex. No Lean theorem was compiled or kernel checked.')
    return results

if __name__ == '__main__':
    output = run()
    text = json.dumps(output, indent=2)
    Path(__file__).with_name('verification_results.json').write_text(text+'\n', encoding='utf-8')
    print(text)
