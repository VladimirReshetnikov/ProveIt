#!/usr/bin/env python3
"""Reproducible exact checks for the accompanying research article.

Run: python3 code/verify.py
Only Python's standard library is required.  No external theorem prover is used.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json
import random
import time
from ordinals import (Ord, ZERO, ONE, OMEGA, finite, mono, from_terms, add,
    mul, natural_add, natural_mul, jacobsthal, fold, pivot_product,
    transition, state_of, sample_points, compare_points, compare_points_by_degree)

ROOT = Path(__file__).resolve().parents[1]
SEED = 20260920
COUNTS: dict[str, int] = {}


def count(name: str, n: int = 1) -> None:
    COUNTS[name] = COUNTS.get(name, 0) + n


def check(condition: bool, description: str, data=None) -> None:
    if not condition:
        raise AssertionError(f'{description}: {data}')


def check_list(xs: tuple[Ord, ...], all_splits: bool = True) -> None:
    direct = pivot_product(xs)
    binary = fold(xs)
    ordinary = fold(xs, mul)
    check(direct == binary, 'pivot versus binary iteration', xs)
    if not all(xs):
        check(direct == ZERO == ordinary, 'absorbing zero', xs)
        return
    check(ordinary <= direct < mul(ordinary, finite(2)), 'factor-two bound', xs)
    check(ordinary.support == direct.support, 'support synchronization', xs)
    check(ordinary.leading == direct.leading, 'leading-monomial synchronization', xs)
    oc, jc = dict(ordinary.terms), dict(direct.terms)
    check(all(oc[e] <= jc[e] for e in oc), 'coefficient domination', xs)
    degree, tail, state = ZERO, 1, 'M'
    for x in xs:
        degree = add(degree, x.degree)
        tail *= x.tail
        state = transition(state, x)
    check(direct.degree == degree, 'degree formula', xs)
    check(direct.tail == tail, 'finite-tail formula', xs)
    check(state == state_of(ordinary, direct), 'three-state automaton', xs)
    natural = fold(xs, natural_mul)
    check(direct <= natural, 'natural-product upper bound', xs)
    if all_splits:
        for k in range(len(xs)+1):
            regrouped = jacobsthal(pivot_product(xs[:k]), pivot_product(xs[k:]))
            check(regrouped == direct, 'split coherence', (xs, k))
            count('split_checks')
    count('nonzero_list_checks')


def main() -> None:
    start = time.perf_counter()
    rng = random.Random(SEED)
    # 3^3 - 1 = 26 positive polynomials below omega^3.
    small = [from_terms((finite(e), c) for e, c in enumerate(cs))
             for cs in product(range(3), repeat=3) if any(cs)]
    for a in [ZERO] + small:
        for b in [ZERO] + small:
            # An independent finite-successor equation checks the binary formula.
            check(jacobsthal(a, add(b, ONE)) == natural_add(jacobsthal(a, b), a),
                  'Jacobsthal successor equation', (a, b))
            if a and b:
                eq = (b.tail <= 1 or len(a.terms) == 1)
                check((jacobsthal(a, b) == mul(a, b)) == eq,
                      'binary equality criterion', (a, b))
            count('binary_pairs')
    for xs in product(small, repeat=3):
        check_list(xs)
        count('exhaustive_triples')

    exponent_pool = [ZERO, ONE, finite(2), finite(3), OMEGA,
                     add(OMEGA, ONE), mul(OMEGA, finite(2)), mono(finite(2)),
                     mono(OMEGA), add(mono(OMEGA), OMEGA)]
    for _ in range(3500):
        xs = tuple(from_terms((e, rng.randint(1, 4))
                              for e in rng.sample(exponent_pool, rng.randint(1, 4)))
                   for _ in range(rng.randint(0, 7)))
        check_list(xs)
        count('nested_exponent_random_lists')
    for n in range(1, 6):
        for zero_position in range(n):
            xs = [rng.choice(small) for _ in range(n)]
            xs[zero_position] = ZERO
            check_list(tuple(xs))
            count('zero_factor_lists')
    check_list(())
    count('empty_list_checks')

    # Concrete order-comparison checks, separate from ordinal-type arithmetic.
    offsets = [ZERO, ONE, finite(2), OMEGA, add(OMEGA, ONE), mono(finite(2))]
    examples = [
        (add(OMEGA, finite(2)),)*3,
        (add(mono(finite(2)), ONE), add(OMEGA, finite(2)), finite(2)),
        (add(OMEGA, ONE), add(mul(OMEGA, finite(2)), ONE), add(OMEGA, ONE)),
        (add(mono(OMEGA), ONE), add(mono(OMEGA), finite(2)), add(OMEGA, ONE)),
    ]
    for factors in examples:
        points = [sample_points(a, offsets) for a in factors]
        tuples = list(product(*points))
        # Exhaustive pairs for the small first family; sampled pairs otherwise.
        pairs = product(tuples, repeat=2) if len(tuples) <= 150 else (
            (rng.choice(tuples), rng.choice(tuples)) for _ in range(25000))
        for x, y in pairs:
            c = compare_points(factors, x, y)
            check(c == compare_points_by_degree(factors, x, y),
                  'prefix-free versus cell-degree comparator', (factors, x, y))
            count('prefix_free_comparator_agreements')
            d = compare_points(factors, y, x)
            check(c == -d, 'comparator antisymmetry', (x, y))
            check((c == 0) == (x == y), 'comparator separation', (x, y))
            if all(p.value <= q.value for p, q in zip(x, y)):
                check(c <= 0, 'componentwise extension', (factors, x, y))
                count('comparable_sampled_pairs')
            count('tuple_pair_checks')
        for _ in range(1000):
            x, y, z = (rng.choice(tuples) for _ in range(3))
            if compare_points(factors, x, y) <= 0 and compare_points(factors, y, z) <= 0:
                check(compare_points(factors, x, z) <= 0, 'comparator transitivity')
            count('tuple_triple_checks')

    a = add(OMEGA, finite(2))
    p = mono(OMEGA)
    illustrative = {
        'a': str(a),
        'ordinary_square': str(mul(a, a)),
        'jacobsthal_square': str(jacobsthal(a, a)),
        'natural_square': str(natural_mul(a, a)),
        'jacobsthal_cube': str(pivot_product((a, a, a))),
        'ordinary_cube': str(fold((a, a, a), mul)),
        'limit_prefix_used_symbolically': str(p),
        'jacobsthal_omega_plus_two_from_proved_reduction': str(mul(p, jacobsthal(a, a))),
        'ordinary_omega_plus_two_from_proved_reduction': str(mul(p, mul(a, a))),
        'discrepancy_before_reset': str(jacobsthal(add(OMEGA, ONE), finite(2))),
        'after_reset_by_omega': str(jacobsthal(jacobsthal(add(OMEGA, ONE), finite(2)), OMEGA)),
    }
    elapsed = round(time.perf_counter() - start, 3)
    result = {
        'status': 'PASS', 'seed': SEED, 'counts': COUNTS,
        'elapsed_seconds': elapsed,
        'scope': 'Exact hereditary CNFs below epsilon_0; finite arithmetic and sampled tuple comparisons.',
        'limitations': [
            'Not a formal proof and not an exhaustive test over all ordinals.',
            'No arbitrary transfinite limit is evaluated by the program.',
            'Symbolic limit examples use the article\'s proved reduction.',
            'The direct and binary routines share a low-level CNF kernel.',
            'Sampled point comparisons do not exhaust the infinite tuple sets.'
        ],
        'examples': illustrative,
    }
    out = ROOT / 'results'
    out.mkdir(exist_ok=True)
    (out / 'verification_results.json').write_text(json.dumps(result, indent=2)+'\n')
    text = ['STATUS: PASS', f'Random seed: {SEED}', '']
    text.extend(f'{k}: {v}' for k, v in COUNTS.items())
    text += ['', f'Elapsed seconds: {elapsed}', '', result['scope'], '']
    text.extend(result['limitations'])
    text += ['', 'EXAMPLES']
    text.extend(f'{k}: {v}' for k, v in illustrative.items())
    (out / 'verification_report.txt').write_text('\n'.join(text)+'\n')
    print('\n'.join(text))


if __name__ == '__main__':
    main()
