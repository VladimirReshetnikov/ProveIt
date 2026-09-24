"""Deterministic regression checks for the accompanying proved formulas.

These finite checks test the implementation and structural lemmas. They are not
formal verification of the transfinite proofs or a search through infinite WPOs.
Run from any working directory: python code/verify.py [--output DIR].
"""
from __future__ import annotations
import argparse
from collections import Counter
import csv
import json
from itertools import product
from pathlib import Path
import platform
import random
import time
from frontiers import (FinitePoset, bits, natural_posets, survivor_value,
    max_topological_sum, powerset_max_type, uniform_invariants,
    lex_sum_max_type, ideal_count_encoding, EXAMPLES)
from ordinals import Ordinal, ZERO, ONE, OMEGA, natural_sum


COUNTS: Counter = Counter()


def require(condition: bool, message: str) -> None:
    COUNTS['assertions'] += 1
    if not condition:
        raise AssertionError(message)


def arithmetic_checks() -> None:
    rng = random.Random(19092026)
    w = OMEGA
    require((w + 1).times_finite(2) == w.times_finite(2) + 1,
            'Ordinary finite multiplication')
    require((w + 1).natural_product(2) == w.times_finite(2) + 2,
            'Natural finite multiplication')
    require(1 + w == w and w + 1 > w, 'Absorption and successor')
    values = [Ordinal.cnf((e, rng.randrange(4)) for e in range(4))
              for _ in range(60)]
    values += [ZERO, ONE, w, Ordinal.omega_power(w),
               Ordinal.omega_power(w + 1) + w + 3]
    for a in values:
        require(Ordinal.from_json(a.to_json()) == a, 'JSON round trip')
        for n in range(6):
            repeated = ZERO
            for _ in range(n):
                repeated += a
            require(a.times_finite(n) == repeated, 'Finite ordinary multiplication')
    for _ in range(500):
        a, b, c = rng.choices(values, k=3)
        require((a+b)+c == a+(b+c), 'Ordinary addition associativity')
        require(a.natural_sum(b) == b.natural_sum(a), 'Natural sum commutativity')
        require(a.natural_product(b) == b.natural_product(a),
                'Natural product commutativity')
        require(a.natural_product(b.natural_sum(c)) ==
                a.natural_product(b).natural_sum(a.natural_product(c)),
                'Natural distributivity')
        COUNTS['arithmetic_random_triples'] += 1
    require(lex_sum_max_type(FinitePoset.from_edges(2, [(0,1)]),
                            [w+1, w+2]) == w.times_finite(2)+2,
            'Lex sum with finite tails')
    require(lex_sum_max_type(FinitePoset.from_edges(2, []),
                            [w+1, w+2]) == w.times_finite(2)+3,
            'Disjoint sum retains tails')


def frontier_checks(q: FinitePoset) -> tuple[list[int], FinitePoset]:
    antichains, index = q.frontier_poset()
    downsets = [q.strict_downset(a) for a in antichains]
    require(len(set(downsets)) == len(antichains), 'Frontier downset injectivity')
    pred = q.predecessors
    full = (1 << q.n)-1
    for a, d in zip(antichains, downsets):
        recovered = sum(1 << x for x in range(q.n)
                        if not d & (1 << x) and not pred[x] & ~d)
        require(recovered == a, 'Frontier = minimal complement of downset')
    for i, a in enumerate(antichains):
        for j, b in enumerate(antichains):
            hoare = all((b & (1 << x)) or (q.successors[x] & b) for x in bits(a))
            require(hoare == (not downsets[i] & ~downsets[j]),
                    'Hoare comparison iff strict-downset inclusion')
    require(index.height() >= 1, 'Nonempty frontier poset')
    return antichains, index


def uniform_census(output: Path) -> None:
    rows = []
    for n in range(1, 7):
        for q in natural_posets(n):
            antichains, index = frontier_checks(q)
            exponents = [Ordinal.finite(a.bit_count()) for a in antichains]
            value, surviving = survivor_value(index, exponents)
            require(value == max_topological_sum(index, exponents),
                    'Uniform formula versus independent whole-stratum DP')
            width = max(a.bit_count() for a in antichains)
            top_coefficient = sum(antichains[i].bit_count() == width for i in surviving)
            require(top_coefficient == sum(a.bit_count() == width for a in antichains),
                    'Leading coefficient counts maximum antichains')
            top_frontier = sum(1 << i for i, s in enumerate(q.successors) if not s)
            unique_max = all(a == top_frontier or a.bit_count() < top_frontier.bit_count()
                             for a in antichains)
            pure = len(value.terms) == 1 and value.terms[0][1] == 1
            require(pure == unique_max, 'Pure-output criterion')
            rows.append(dict(n=n, relation=';'.join(f'{i}<{j}' for i in range(n)
                                                   for j in bits(q.successors[i])),
                             frontiers=len(antichains), frontier_height=index.height(),
                             width=width, max_type=str(value)))
            COUNTS[f'naturally_labelled_posets_n{n}'] += 1
            COUNTS['uniform_posets'] += 1
    with (output/'poset_census.csv').open('w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)


def weighted_checks() -> None:
    for n in range(1, 5):
        for q in natural_posets(n):
            for weights in product(range(1,4), repeat=n):
                value, _, exponents, index = powerset_max_type(
                    q, [Ordinal.finite(x) for x in weights])
                require(value == max_topological_sum(index, exponents),
                        'Weighted frontiers versus whole-stratum DP')
                COUNTS['weighted_frontier_cases'] += 1
            for weights in product(range(3), repeat=n):
                exponents = [Ordinal.finite(x) for x in weights]
                require(survivor_value(q, exponents)[0] ==
                        max_topological_sum(q, exponents),
                        'General pure-stratum absorption including exponent zero')
                COUNTS['pure_stratum_cases'] += 1
    exotic = [ONE, OMEGA+1, Ordinal.omega_power(OMEGA)]
    for q in EXAMPLES.values():
        for shift in range(3):
            weights = [exotic[(i+shift)%3] for i in range(q.n)]
            value, _, exponents, index = powerset_max_type(q, weights)
            require(value == max_topological_sum(index, exponents),
                    'Hereditary-CNF weighted case')
            COUNTS['hereditary_ordinal_cases'] += 1


def profile_from_generators(q: FinitePoset, generator_mask: int, cap: int) -> tuple[int,...]:
    support = sum(1 << i for i in range(q.n)
                  if any(generator_mask & (1 << (cap*i+k)) for k in range(cap)))
    return tuple(cap+1 if q.successors[i] & support else
                 max((k+1 for k in range(cap)
                      if generator_mask & (1 << (cap*i+k))), default=0)
                 for i in range(q.n))


def profile_checks() -> None:
    cap = 2
    infinity = cap+1  # Symbolically the WHOLE omega-fiber, not a finite cutoff.
    for n in range(1,5):
        for q in natural_posets(n):
            antichains, index = q.frontier_poset()
            downsets = [q.strict_downset(a) for a in antichains]
            d_to_i = {d:i for i,d in enumerate(downsets)}
            generated = {profile_from_generators(q, g, cap)
                         for g in range(1 << (n*cap))}
            canonical: set[tuple[int,...]] = set()
            for a, d in zip(antichains, downsets):
                active = list(bits(a))
                for coordinates in product(range(cap+1), repeat=len(active)):
                    support = sum(1 << x for x,c in zip(active,coordinates) if c)
                    if q.strict_downset(support) != d:
                        continue
                    profile = [infinity if d & (1 << x) else 0 for x in range(n)]
                    for x,c in zip(active,coordinates):
                        profile[x] = c
                    canonical.add(tuple(profile))
            require(generated == canonical, 'Canonical stratum representation')
            profiles = sorted(generated)
            for p in profiles:
                d = sum(1 << x for x,c in enumerate(p) if c == infinity)
                i = d_to_i[d]
                a = antichains[i]
                for j in [i]+list(bits(index.successors[i])):
                    b, e = antichains[j], downsets[j]
                    upper = tuple(infinity if e & (1 << x) else
                                  max(1,p[x]) if b & (1 << x) else 0
                                  for x in range(n))
                    require(upper in generated and all(x<=y for x,y in zip(p,upper)),
                            'Constructed upward-cofinal witness')
                for r in profiles:
                    inclusion = all(x <= y for x,y in zip(p,r))
                    generators_p = [(x,c-1) for x,c in enumerate(p) if 0<c<infinity]
                    generators_r = [(x,c-1) for x,c in enumerate(r) if 0<c<infinity]
                    hoare = all(any((x==y and k<=l) or q.successors[x] & (1 << y)
                                    for y,l in generators_r) for x,k in generators_p)
                    require(inclusion == hoare, 'Hoare order equals profile inclusion')
                    if inclusion:
                        e = sum(1 << x for x,c in enumerate(r) if c == infinity)
                        require(not d & ~e, 'Order respects frontier indices')
                    COUNTS['profile_pairs'] += 1
            COUNTS['finite_profiles'] += len(profiles)
            COUNTS['profile_posets'] += 1


def sum_posets(a: FinitePoset, b: FinitePoset, ordinal: bool) -> FinitePoset:
    edges = [(i,j) for i in range(a.n) for j in bits(a.successors[i])]
    edges += [(a.n+i,a.n+j) for i in range(b.n) for j in bits(b.successors[i])]
    if ordinal:
        edges += [(i,a.n+j) for i in range(a.n) for j in range(b.n)]
    return FinitePoset.from_edges(a.n+b.n, edges)


def series_parallel_checks() -> None:
    rng = random.Random(271828)
    def build(n: int):
        if n == 1:
            return FinitePoset.from_edges(1, []), OMEGA, 1
        k = rng.randrange(1,n)
        a,oa,ha = build(k); b,ob,hb = build(n-k)
        ordinal = bool(rng.randrange(2))
        return (sum_posets(a,b,ordinal), oa+ob if ordinal else oa.natural_product(ob),
                ha+hb if ordinal else ha+hb-1)
    for _ in range(500):
        q, expected_o, expected_h_coefficient = build(rng.randrange(1,10))
        result = uniform_invariants(q)
        require(Ordinal.from_json(result['max_type_cnf']) == expected_o,
                'Series-parallel recursive maximal type')
        require(result['frontier_height'] == expected_h_coefficient,
                'Series-parallel recursive height coefficient')
        COUNTS['series_parallel_cases'] += 1


def counting_checks() -> None:
    for n in range(1,6):
        for r in natural_posets(n):
            q = ideal_count_encoding(r)
            maximum = [a for a in q.antichains() if a.bit_count() == n]
            require(len(maximum) == len(r.ideals()), 'Ideal-count coefficient reduction')
            decoded = {a >> n for a in maximum}
            require(decoded == set(r.ideals()), 'Explicit ideal/antichain bijection')
            COUNTS['counting_reductions'] += 1



def lexicographic_checks() -> None:
    """Compare CNF truncation with DP on the fully expanded pure-block index."""
    choices = [Ordinal.finite(2), OMEGA+1, Ordinal.omega_power(2)+OMEGA+1]
    for n in range(1,5):
        for q in natural_posets(n):
            for types in product(choices, repeat=n):
                labels = []
                exponents = []
                for i,value in enumerate(types):
                    for e,c in value.terms:
                        labels.extend([i]*c)
                        exponents.extend([e]*c)
                edges = [(i,j) for i in range(len(labels)) for j in range(len(labels))
                         if (labels[i] == labels[j] and i < j) or
                            (q.successors[labels[i]] & (1 << labels[j]))]
                expanded = FinitePoset.from_edges(len(labels),edges)
                require(lex_sum_max_type(q,list(types)) ==
                        max_topological_sum(expanded,exponents),
                        'Nonuniform CNF truncation versus expanded-block DP')
                COUNTS['lexicographic_cnf_cases'] += 1
    require(lex_sum_max_type(FinitePoset.from_edges(3,[(0,1),(1,2)]),
                            [OMEGA,ZERO,ONE]) == OMEGA+1,
            'Zero fibers are deleted without losing transitive comparisons')
    require(uniform_invariants(FinitePoset(()))['max_type'] == '1',
            'Empty skeleton has singleton finitary powerset')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data')
    args = parser.parse_args(); args.output.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    for check in [arithmetic_checks, lambda: uniform_census(args.output),
                  weighted_checks, profile_checks, series_parallel_checks, counting_checks,
                  lexicographic_checks]:
        print('Checking', getattr(check, '__name__', str(check)), flush=True)
        check()
    report = dict(status='PASS', python=platform.python_version(),
                  elapsed_seconds=round(time.monotonic()-start,3),
                  counts=dict(COUNTS),
                  scope='Finite structural and implementation checks; not a formal proof '
                        'of transfinite statements. Posets are naturally labelled, '
                        'not isomorphism-reduced.')
    (args.output/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
