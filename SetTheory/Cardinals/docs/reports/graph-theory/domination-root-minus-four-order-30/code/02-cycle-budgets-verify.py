#!/usr/bin/env python3
"""Exact certificates for domination-polynomial cycle obstructions.

Python 3.10+, standard library only. No network, cached catalogue, floating-point
arithmetic, or external graph library is needed. Run from any working directory:
    python3 code/verify.py
The mathematical reductions and their all-graph scope are proved in article.tex.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from math import prod
from pathlib import Path
import random
import time

Edge = tuple[int, int]
Matrix = tuple[tuple[int, ...], ...]
W = ((1, 0, 0), (0, -1, 0), (0, 0, -1))
F1 = ((1, 1, 1), (1, 1, 0), (1, 0, 1))
EXPECTED_SPECTRA = {0: {1}, 1: {1, 3}, 2: {1, 3, 7, 9},
                    3: {1, 3, 5, 7, 9, 11, 15, 17, 21, 27}}


def matmul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


def neg(v: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(-x for x in v)


BASE_STATES = {(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
               (1, -1, 0), (1, 0, -1), (0, 1, -1)}
STATES = BASE_STATES | {neg(s) for s in BASE_STATES}
ORDINARY_STATES = {(-1, 0, 1), (1, 0, -1), (0, 1, 0), (0, -1, 0)}


def adjacency(n: int, edges: list[Edge]) -> list[list[int]]:
    out: list[list[int]] = [[] for _ in range(n)]
    seen: set[Edge] = set()
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError('A simple graph with vertices 0,...,n-1 is required')
        e = tuple(sorted((u, v)))
        if e in seen:
            raise ValueError('Repeated edge in simple graph')
        seen.add(e)
        out[u].append(v)
        out[v].append(u)
    return out


def spanning_forest(n: int, edges: list[Edge]) -> tuple[list[Edge], list[Edge]]:
    parent = list(range(n))
    def root(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    forest, feedback = [], []
    for u, v in edges:
        a, b = root(u), root(v)
        if a == b:
            feedback.append((u, v))
        else:
            parent[a] = b
            forest.append((u, v))
    return forest, feedback


def brute_polynomial(n: int, edges: list[Edge]) -> list[int]:
    adj = adjacency(n, edges)
    masks = [(1 << i) | sum(1 << j for j in adj[i]) for i in range(n)]
    cover = [0] * (1 << n)
    out = [0] * (n + 1)
    full = (1 << n) - 1
    for s in range(1 << n):
        if s:
            bit = s & -s
            cover[s] = cover[s ^ bit] | masks[bit.bit_length() - 1]
        if cover[s] == full:
            out[s.bit_count()] += 1
    return out


def evaluate(coeffs: list[int], x: int) -> int:
    ans = 0
    for c in reversed(coeffs):
        ans = ans * x + c
    return ans


def constrained_forest(n: int, edges: list[Edge], pins: list[int],
                       free: set[int]) -> int:
    """Alternating sum; pin -1=unrestricted, 0=absent, 1=selected.

    Free vertices have no domination requirement. All other vertices must be
    dominated. Returns -1, 0 or 1, including inconsistent cases checked by caller.
    """
    adj = adjacency(n, edges)
    parent = [-2] * n
    order, roots = [], []
    for start in range(n):
        if parent[start] != -2:
            continue
        roots.append(start)
        parent[start] = -1
        stack = [start]
        while stack:
            v = stack.pop()
            order.append(v)
            for u in adj[v]:
                if u == parent[v]:
                    continue
                if parent[u] != -2:
                    raise ValueError('constrained_forest received a cyclic graph')
                parent[u] = v
                stack.append(u)
    state = [(0, 0, 0)] * n
    for v in reversed(order):
        p = q = r = 1
        for u in adj[v]:
            if parent[u] == v:
                a, b, c = state[u]
                p *= a + b + c
                q *= a + b
                r *= b
        a, b, c = -p, q - r, r
        if v in free:
            b, c = b + c, 0
        if pins[v] == 1:
            b = c = 0
        elif pins[v] == 0:
            a = 0
        state[v] = (a, b, c)
        assert state[v] in STATES, (v, state[v])
    answer = prod(state[r][0] + state[r][1] for r in roots)
    assert answer in (-1, 0, 1)
    return answer


def feedback_evaluation(n: int, edges: list[Edge]) -> tuple[int, Counter]:
    """The article's three-way feedback-edge partition, with exact leaf counts."""
    forest, extra = spanning_forest(n, edges)
    counts: Counter = Counter({-1: 0, 0: 0, 1: 0})
    for choices in product(range(3), repeat=len(extra)):
        pins, free, consistent = [-1] * n, set(), True
        for (u, v), choice in zip(extra, choices):
            if choice == 0:    # u selected; v unrestricted and externally dominated
                assignments = ((u, 1),)
                free.add(v)
            elif choice == 1:  # u absent, v selected; u externally dominated
                assignments = ((u, 0), (v, 1))
                free.add(u)
            else:              # both absent
                assignments = ((u, 0), (v, 0))
            for vertex, wanted in assignments:
                if pins[vertex] not in (-1, wanted):
                    consistent = False
                pins[vertex] = wanted
        term = constrained_forest(n, forest, pins, free) if consistent else 0
        counts[term] += 1
    return counts[1] - counts[-1], counts


def path_matrix_brute(length: int) -> Matrix:
    """Independent selected-bit/endpoint-inclusion-exclusion path calculation."""
    rows = []
    for a in range(3):
        row = []
        for b in range(3):
            answer = 0
            for inside in product((0, 1), repeat=length - 1):
                bits = (int(a == 1),) + inside + (int(b == 1),)
                if a == 2 and bits[1]:
                    continue
                if b == 2 and bits[-2]:
                    continue
                if all(bits[i-1] or bits[i] or bits[i+1]
                       for i in range(1, length)):
                    answer += (-1) ** sum(inside)
            row.append(answer)
        rows.append(tuple(row))
    return tuple(rows)


F = {1: F1}
for length in range(2, 5):
    F[length] = matmul(matmul(F[length-1], W), F1)


def kernel_value(n: int, edges: list[Edge], lengths: tuple[int, ...]) -> int:
    answer = 0
    for states in product(range(3), repeat=n):
        term = (-1) ** sum(s != 0 for s in states)
        for (u, v), length in zip(edges, lengths):
            term *= F[1 + (length-1) % 4][states[u]][states[v]]
            if not term:
                break
        answer += term
    return answer


def generate_kernels(beta: int) -> list[tuple[int, list[Edge]]]:
    """Exhaust ALL reduced connected multigraphs, modulo all vertex permutations.

    Loops count twice toward degree. n <= 2*beta-2 and m=n+beta-1.
    No graph-isomorphism package or externally supplied list is used.
    """
    out = []
    for n in range(1, 2 * beta - 1):
        pair_types = list(combinations_with_replacement(range(n), 2))
        known: set[tuple[Edge, ...]] = set()
        for indices in combinations_with_replacement(range(len(pair_types)), n+beta-1):
            edges = [pair_types[i] for i in indices]
            degree = [0] * n
            for u, v in edges:
                degree[u] += 1
                degree[v] += 1
            if min(degree) < 3:
                continue
            forest, _ = spanning_forest(n, edges)
            if len(forest) != n - 1:
                continue
            code = min(tuple(sorted(tuple(sorted((p[u], p[v]))) for u, v in edges))
                       for p in permutations(range(n)))
            if code not in known:
                known.add(code)
                out.append((n, list(code)))
    return sorted(out, key=lambda item: (item[0], item[1]))


def simple_lengths(edges: list[Edge], residues: tuple[int, ...]) -> tuple[int, ...]:
    """Realize any residue assignment by a SIMPLE subdivision."""
    direct: set[Edge] = set()
    result = []
    for (u, v), ell in zip(edges, residues):
        if u == v:
            while ell < 3:
                ell += 4
        elif ell == 1:
            if (u, v) in direct:
                ell += 4
            direct.add((u, v))
        result.append(ell)
    return tuple(result)


def expand(n: int, edges: list[Edge], lengths: tuple[int, ...]) -> tuple[int, list[Edge]]:
    result, next_vertex = [], n
    for (u, v), ell in zip(edges, lengths):
        path = [u] + list(range(next_vertex, next_vertex + ell - 1)) + [v]
        next_vertex += ell - 1
        result.extend(zip(path[:-1], path[1:]))
    adjacency(next_vertex, result)  # validates simplicity
    return next_vertex, result


def buffered_join(g: tuple[int, list[Edge]], h: tuple[int, list[Edge]]) -> tuple[int, list[Edge]]:
    n, ge = g
    m, he = h
    z, leaf = n+m, n+m+1
    return n+m+2, ge + [(u+n, v+n) for u, v in he] + [(0, z), (n, z), (z, leaf)]


def cycle(n: int) -> tuple[int, list[Edge]]:
    return n, [(i, (i+1) % n) for i in range(n)]


def check_states() -> dict:
    transformed = {tuple((a+b+c, a+b, b)) for a, b, c in STATES}
    # Coordinatewise closure proves arbitrary child counts, not only bounded arity.
    assert (1, 1, 1) in transformed
    for t, u in product(transformed, repeat=2):
        assert tuple(x*y for x, y in zip(t, u)) in transformed
    for p, q, r in transformed:
        s = (-p, q-r, r)
        assert s in STATES
        for free, pin in product((False, True), (-1, 0, 1)):
            a, b, c = s
            if free:
                b, c = b+c, 0
            if pin == 1:
                b = c = 0
            if pin == 0:
                a = 0
            assert (a, b, c) in STATES
    assert all(abs(a+b) <= 1 for a, b, c in STATES)
    ordinary_transformed = {(a+b+c, a+b, b) for a, b, c in ORDINARY_STATES}
    assert (1, 1, 1) in ordinary_transformed
    for a, b in product(ordinary_transformed, repeat=2):
        assert tuple(x*y for x, y in zip(a, b)) in ordinary_transformed
    assert all((-p, q-r, r) in ORDINARY_STATES for p, q, r in ordinary_transformed)
    transfer = matmul(W, F1)
    power = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    for _ in range(4):
        power = matmul(power, transfer)
    assert power == ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    for ell in range(1, 13):
        assert path_matrix_brute(ell) == F[1+(ell-1) % 4]
    return {'signed_forest_states': len(STATES), 'path_lengths_checked': 12,
            'arbitrary_arity_product_closure': True, 'transfer_fourth_power_identity': True}


def exhaustive_small() -> dict:
    count = 0
    polynomial_roots = 0
    for n in range(6):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [e for i, e in enumerate(pairs) if mask >> i & 1]
            coeffs = brute_polynomial(n, edges)
            actual = evaluate(coeffs, -1)
            b = len(spanning_forest(n, edges)[1])
            calculated, terms = feedback_evaluation(n, edges)
            assert actual == calculated
            assert sum(terms.values()) == 3**b
            assert actual % 2 == 1 and abs(actual) <= 3**b
            if b <= 3:
                assert abs(actual) in EXPECTED_SPECTRA[b]
            # Check the elementary modular/root implications on full polynomials.
            for k in range(2, 16):
                if evaluate(coeffs, -k) == 0:
                    polynomial_roots += 1
                    assert k % 2 == 0 and actual % (k-1) == 0
            count += 1
    assert count == 1100
    return {'labeled_graphs_through_order_5': count, 'integer_root_instances_checked': polynomial_roots}


def constrained_brute(n: int, edges: list[Edge], pins: list[int], free: set[int]) -> int:
    adj = adjacency(n, edges)
    answer = 0
    for bits in product((0, 1), repeat=n):
        if any(p != -1 and p != s for p, s in zip(pins, bits)):
            continue
        if all(v in free or bits[v] or any(bits[u] for u in adj[v]) for v in range(n)):
            answer += (-1) ** sum(bits)
    return answer


def randomized_checks() -> dict:
    rng = random.Random(20260930)
    for _ in range(300):
        n = rng.randrange(1, 11)
        edges = [(i, rng.randrange(i)) for i in range(1, n) if rng.randrange(4)]
        pins = [rng.choice((-1, 0, 1)) for _ in range(n)]
        free = {v for v in range(n) if rng.randrange(2)}
        assert constrained_forest(n, edges, pins, free) == constrained_brute(n, edges, pins, free)
    for _ in range(120):
        n = rng.randrange(2, 11)
        edges = [(i, rng.randrange(i)) for i in range(1, n)]
        present = {tuple(sorted(e)) for e in edges}
        choices = [e for e in combinations(range(n), 2) if e not in present]
        rng.shuffle(choices)
        edges += choices[:rng.randrange(min(4, len(choices))+1)]
        assert feedback_evaluation(n, edges)[0] == evaluate(brute_polynomial(n, edges), -1)
    return {'seed': 20260930, 'constrained_forests': 300, 'additional_graphs': 120}


def kernel_certificates() -> tuple[dict, list[dict], dict]:
    records = []
    witnesses: dict[int, dict] = {}
    residue_count, expanded_checks = 0, 0
    for beta in (2, 3):
        kernels = generate_kernels(beta)
        assert len(kernels) == {2: 3, 3: 15}[beta]
        for index, (n, edges) in enumerate(kernels):
            values = set()
            best_size: dict[int, int] = {}
            for residues in product(range(1, 5), repeat=len(edges)):
                value = kernel_value(n, edges, residues)
                values.add(value)
                residue_count += 1
                lengths = simple_lengths(edges, residues)
                order = n + sum(ell-1 for ell in lengths)
                av = abs(value)
                if av not in witnesses or (beta, order) < (witnesses[av]['beta'], witnesses[av]['order']):
                    order, expanded_edges = expand(n, edges, lengths)
                    witnesses[av] = {'beta': beta, 'order': order, 'edges': expanded_edges,
                                     'value': value, 'kernel_index': index,
                                     'kernel_edges': edges, 'lengths': lengths}
                if order <= 9 and order < best_size.get(value, 1000):
                    nn, ee = expand(n, edges, lengths)
                    assert evaluate(brute_polynomial(nn, ee), -1) == value
                    expanded_checks += 1
                    best_size[value] = order
            records.append({'beta': beta, 'index': index, 'vertices': n, 'edges': edges,
                            'signed_values': sorted(values), 'absolute_values': sorted({abs(v) for v in values}),
                            'residue_assignments': 4**len(edges)})
    # Complete cumulative spectrum: products across components use additive beta.
    bare = {0: {1}, 1: {1, 3}, 2: set(), 3: set()}
    for rec in records:
        bare[rec['beta']].update(rec['absolute_values'])
    cumulative = {0: {1}}
    for b in range(1, 4):
        values = set(cumulative[b-1]) | bare[b]
        for i in range(1, b):
            values |= {x*y for x in cumulative[i] for y in cumulative[b-i]}
        cumulative[b] = values
        assert values == EXPECTED_SPECTRA[b], (b, values)
    # Explicit connected examples for product-only values.
    for value, factors in ((9, (3, 3)), (21, (3, 7)), (27, (3, 3, 3))):
        g = cycle(4)
        for f in factors[1:]:
            h = cycle(4) if f == 3 else (witnesses[7]['order'], [tuple(e) for e in witnesses[7]['edges']])
            g = buffered_join(g, h)
        nn, ee = g
        actual = feedback_evaluation(nn, ee)[0]
        assert abs(actual) == value
        witnesses[value] = {'beta': len(spanning_forest(nn, ee)[1]), 'order': nn,
                            'edges': ee, 'value': actual, 'construction': 'leaf-buffered join'}
    witnesses[1] = {'beta': 0, 'order': 1, 'edges': [], 'value': -1}
    witnesses[3] = {'beta': 1, 'order': 4, 'edges': cycle(4)[1], 'value': 3}
    for av, witness in witnesses.items():
        nn, ee = witness['order'], [tuple(e) for e in witness['edges']]
        calculated = feedback_evaluation(nn, ee)[0]
        assert calculated == witness['value'] and abs(calculated) == av
        assert len(spanning_forest(nn, ee)[1]) == witness['beta']
        if nn <= 16:
            assert evaluate(brute_polynomial(nn, ee), -1) == calculated
    # Equality examples of arbitrary size are proved in the article; check b=1..6.
    g = cycle(4)
    for b in range(1, 7):
        if b > 1:
            g = buffered_join(g, cycle(4))
        assert len(spanning_forest(*g)[1]) == b
        assert feedback_evaluation(*g)[0] == (-1)**(b-1) * 3**b
    return ({'kernel_counts': {'2': 3, '3': 15}, 'total_residue_assignments': residue_count,
             'beta3_residue_assignments': sum(r['residue_assignments'] for r in records if r['beta']==3),
             'small_expanded_kernel_brute_checks': expanded_checks,
             'cumulative_absolute_spectra': {str(k): sorted(v) for k, v in cumulative.items()},
             'sharpness_examples_beta_1_through_6': True}, records,
            {str(k): v for k, v in sorted(witnesses.items())})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    started = time.perf_counter()
    result = {'state_and_transfer_checks': check_states(),
              'small_graph_checks': exhaustive_small(), 'randomized_checks': randomized_checks()}
    result['kernel_checks'], records, witnesses = kernel_certificates()
    result['status'] = 'PASS'
    result['elapsed_seconds'] = round(time.perf_counter() - started, 3)
    result['scope'] = ('Exact finite certificates and independent implementation checks; '
                       'the all-graph reductions are conventional proofs in article.tex, not Lean formalizations.')
    for folder in ('data', 'results'):
        (args.output_dir / folder).mkdir(parents=True, exist_ok=True)
    for relative, obj in [('results/verification.json', result), ('data/kernel_certificate.json', records),
                          ('data/spectrum_witnesses.json', witnesses)]:
        (args.output_dir / relative).write_text(json.dumps(obj, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
