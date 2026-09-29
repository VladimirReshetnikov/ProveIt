"""Deterministic finite/symbolic checks, NOT a proof-assistant formalization.

The fixed default run is reproducible using Python 3.10+. Results are saved to
verification.json in the package root. No dependencies outside the stdlib.
"""
from __future__ import annotations
import copy
import itertools
import json
from pathlib import Path
import random
import sys
from ordinals import Ordinal, ZERO, ONE, OMEGA, ordinal_sum, natural_sum, product_height
from heights import Poset, bits, pure_height, frontier_height, expand, check_certificate, solve, point_rank

ROOT = Path(__file__).resolve().parents[1]
COUNTS: dict[str, int] = {}


def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(f'Failed category: {category}, case {COUNTS.get(category, 0) + 1}')
    COUNTS[category] = COUNTS.get(category, 0) + 1


def all_naturally_labelled_posets(n: int):
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = [pairs[k] for k in bits(mask)]
        p = Poset.from_edges(n, edges)
        if sum(x.bit_count() for x in p.succ) == len(edges):
            yield p


def path_enumeration(p: Poset, weights: list[Ordinal]) -> Ordinal:
    """Enumerate every linear extension; deliberately no DP or cost helper."""
    full = (1 << p.n) - 1
    best = ZERO
    def visit(sequence: list[int], remaining: set[int]) -> None:
        nonlocal best
        if not remaining:
            active: set[int] = set()
            costs = []
            for v in sequence:
                retired = {a for a in active if p.succ[a] >> v & 1}
                costs.append(max([ONE] + [weights[a] for a in retired]))
                active.difference_update(retired)
                active.add(v)
            costs.append(max([ONE] + [weights[a] for a in active]))
            best = max(best, ordinal_sum(costs))
            return
        for v in sorted(remaining):
            if not any(p.pred[v] >> a & 1 for a in remaining):
                visit(sequence + [v], remaining - {v})
    visit([], set(range(p.n)))
    return best


def uniform_expected(p: Poset, lam: Ordinal) -> Ordinal:
    frontiers = p.maximal_antichains()
    d = {a: p.downclosure(a) for a in frontiers}
    heights = {}
    for b in sorted(frontiers, key=lambda a: d[a].bit_count()):
        heights[b] = 1 + max([0] + [heights[a] for a in heights if d[a] & ~d[b] == 0])
    return ordinal_sum([lam] * max(heights.values()))


def finite_support_check(p: Poset, lengths: list[int]) -> None:
    # Independently enumerate support-antichain tuples and actual downsets.
    items = [(q, i) for q, n in enumerate(lengths) for i in range(n)]
    states = []
    masks = []
    for support in range(1 << p.n):
        if any(p.succ[q] & support for q in bits(support)):
            continue
        indices = list(bits(support))
        for values in itertools.product(*(range(lengths[q]) for q in indices)):
            state = dict(zip(indices, values))
            down = 0
            for i, (r, k) in enumerate(items):
                if any((r == q and k <= x) or (p.succ[r] >> q & 1)
                       for q, x in state.items()):
                    down |= 1 << i
            states.append(state)
            masks.append(down)
    check(len(masks) == len(set(masks)), 'finite_support_injectivity')
    for i, left in enumerate(states):
        for j, right in enumerate(states):
            hoare = all(any(a == b or p.succ[a] >> b & 1 for b in right) for a in left)
            shared = all(left[a] <= right[a] for a in left.keys() & right.keys())
            check((hoare and shared) == (masks[i] & ~masks[j] == 0), 'finite_support_order_pairs')
    # Direct finite rank from subset inclusion, independent of ordinal path costs.
    ranks = {}
    for mask in sorted(masks, key=int.bit_count):
        ranks[mask] = max([0] + [r + 1 for old, r in ranks.items() if old & ~mask == 0])
    direct = max(ranks.values()) + 1
    data = {'n': p.n, 'edges': [[i, j] for i in range(p.n) for j in bits(p.succ[i])],
            'fiber_types': lengths}
    for state, mask in zip(states, masks):
        result = point_rank(data, [[q, x] for q, x in state.items()])
        check(Ordinal.from_json(result['rank']) == Ordinal.finite(ranks[mask]),
              'exact_local_ranks_on_finite_inputs')
    refined, weights, _ = expand(p, [Ordinal.finite(n) for n in lengths])
    height, _ = pure_height(refined, weights)
    check(height == Ordinal.finite(direct), 'finite_direct_rank')
    check(direct == sum(lengths) + 1, 'finite_rank_equals_size_plus_one')


def sampled_ordinal_arithmetic() -> None:
    samples = []
    for a, b, c in itertools.product(range(3), repeat=3):
        terms = tuple((Ordinal.finite(e), coeff) for e, coeff in [(2, a), (1, b), (0, c)] if coeff)
        samples.append(Ordinal(terms))
    for x in samples:
        check(Ordinal.from_json(x.to_json()) == x, 'ordinal_json_roundtrip')
    for x, y, z in itertools.product(samples, repeat=3):
        check((x + y) + z == x + (y + z), 'ordinary_addition_associativity')
        check(x.natural_sum(y).natural_sum(z) == x.natural_sum(y.natural_sum(z)),
              'natural_sum_associativity')
    for exponent in [ZERO, ONE, Ordinal.finite(2), Ordinal.finite(3), OMEGA]:
        w = Ordinal.omega_power(exponent)
        for p, delta in itertools.product(samples, repeat=2):
            if delta < w:
                check(p.natural_sum(delta) < p + w, 'absorption_inequality')
    check(OMEGA + Ordinal.omega_power(Ordinal.finite(2)) == Ordinal.omega_power(Ordinal.finite(2)),
          'noncommutative_regression')
    check(OMEGA.natural_sum(Ordinal.omega_power(Ordinal.finite(2))) != OMEGA + Ordinal.omega_power(Ordinal.finite(2)),
          'noncommutative_regression')


def main() -> None:
    sampled_ordinal_arithmetic()
    census = {}
    pure = [ONE, OMEGA, Ordinal.omega_power(Ordinal.finite(2))]
    for n in range(6):
        count = 0
        for p in all_naturally_labelled_posets(n):
            count += 1
            profiles = list(itertools.product(pure, repeat=n)) if n <= 3 else [
                tuple(pure[(v + shift) % 3] for v in range(n)) for shift in range(3)]
            if n >= 4:
                profiles += [tuple(OMEGA for _ in range(n)),
                             tuple(pure[2] if v % 2 else OMEGA for v in range(n))]
            for profile in profiles:
                weights = list(profile)
                actual, certificate = pure_height(p, weights)
                check(actual == path_enumeration(p, weights), 'dp_vs_all_linear_extensions')
                check(check_certificate(certificate), 'full_certificate_checks')
                if n and all(w > ONE for w in weights):
                    check(actual == frontier_height(p, weights), 'support_vs_maximal_frontiers')
            if n:
                for lam in [OMEGA, pure[2]]:
                    actual, _ = pure_height(p, [lam] * n)
                    check(actual == uniform_expected(p, lam), 'uniform_frontier_recovery')
            if n <= 3:
                for lengths in itertools.product(range(3), repeat=n):
                    finite_support_check(p, list(lengths))
        census[str(n)] = count
    # Structured finite tests beyond three vertices.
    rng = random.Random(20260924)
    for _ in range(80):
        n = rng.randrange(4, 7)
        p = Poset.from_edges(n, [(i, j) for i in range(n) for j in range(i + 1, n)
                               if rng.randrange(3) == 0])
        finite_support_check(p, [rng.randrange(2) for _ in range(n)])
    # Known Cartesian product-height formula: mixed CNFs, zeros, finite tails.
    pool = [ZERO, ONE, Ordinal.finite(2), OMEGA, OMEGA + ONE,
            OMEGA + OMEGA, pure[2], pure[2] + OMEGA, pure[2] + ONE]
    for n in range(4):
        p = Poset.from_edges(n, [])
        for fibers in itertools.product(pool, repeat=n):
            refined, weights, _ = expand(p, list(fibers))
            actual, cert = pure_height(refined, weights)
            expected = product_height([ONE + alpha for alpha in fibers])
            check(actual == expected, 'disjoint_chains_vs_product_formula')
    # Non-natural finite labels (including recursive CNF exponents).
    new_exponents = [ZERO, OMEGA, OMEGA + ONE]
    def relabel(x: Ordinal) -> Ordinal:
        return Ordinal(tuple((new_exponents[e.terms[0][1] if e else 0], c) for e, c in x.terms))
    for _ in range(100):
        n = rng.randrange(1, 7)
        p = Poset.from_edges(n, [(i, j) for i in range(n) for j in range(i + 1, n)
                               if rng.randrange(3) == 0])
        weights = [pure[rng.randrange(3)] for _ in range(n)]
        a, _ = pure_height(p, weights)
        b, _ = pure_height(p, [relabel(w) for w in weights])
        check(relabel(a) == b, 'ordinal_scale_invariance')
    # Fixed examples, with certificates saved alongside the inputs.
    expected_examples = {
        'persistent': pure[2],
        'weighted_N': Ordinal.omega_power(Ordinal.finite(3)) + pure[2],
        'weighted_N_three_terms': Ordinal.omega_power(Ordinal.finite(3)) + pure[2] + pure[2],
        'complete_two_levels': pure[2] + pure[2],
        'finite_top': OMEGA + ONE,
        'mixed_CNF': None,
        'transfinite_exponent': None,
    }
    example_results = {}
    last = None
    for name, expected in expected_examples.items():
        data = json.loads((ROOT / 'examples' / f'{name}.json').read_text())
        cert = solve(data)
        value = Ordinal.from_json(cert['height'])
        if expected is not None:
            check(value == expected, 'worked_examples')
        check(check_certificate(cert), 'example_certificates')
        (ROOT / 'examples' / f'{name}_certificate.json').write_text(json.dumps(cert, indent=2) + '\n')
        example_results[name] = {'height': cert['height_text'], 'expanded_vertices': cert['vertices'],
                                 'ideals': cert['ideal_count']}
        last = cert
    point_data = json.loads((ROOT / 'examples' / 'point_rank.json').read_text())
    point = point_rank(point_data, point_data['generators'])
    check(Ordinal.from_json(point['rank']) == OMEGA + OMEGA + Ordinal.finite(5),
          'infinite_point_rank_example')
    (ROOT / 'examples' / 'point_rank_certificate.json').write_text(json.dumps(point, indent=2) + '\n')
    example_results['point_rank'] = {'rank': point['rank_text']}
    corrupted = copy.deepcopy(last)
    corrupted['height'] = 0
    check(not check_certificate(corrupted), 'corrupted_certificate_rejected')
    for bad in [-1, True, [[1, 0]], [[0, 1], [1, 1]]]:
        try:
            Ordinal.from_json(bad)
        except (TypeError, ValueError):
            check(True, 'invalid_ordinal_rejected')
        else:
            check(False, 'invalid_ordinal_rejected')
    try:
        Poset.from_edges(2, [(0, 1), (1, 0)])
    except ValueError:
        check(True, 'cyclic_input_rejected')
    report = {'status': 'PASS', 'date': '2026-09-24', 'python': sys.version.split()[0],
              'seed': 20260924, 'naturally_labelled_poset_census': census,
              'checks': COUNTS, 'total_assertions': sum(COUNTS.values()),
              'examples': example_results,
              'scope': 'Finite structure and exact symbolic ordinal checks, not formal verification of transfinite theorems.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
