"""Reproduce all finite audits and tables. Standard library, Python >= 3.10.

Run from any directory. Default output is ../data relative to this script;
--output-dir redirects it. Universal proofs are in article.tex.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
import random
from collections import Counter
from itertools import product
from math import factorial
from pathlib import Path
from isolation import (
    admissible, bounded_positive, canonical_center, compositions, deletion_test,
    extremal_count, feasible, full_output_test, gap_vector, literal_singleton_degrees,
    literal_word, maximal_targets, minimum_length, minimum_total, partitions, predecessors, mandatory_extremal_target,
)


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'data')
    args = parser.parse_args()
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    report: dict = {'status': 'RUNNING', 'python': platform.python_version(),
                    'seed': 20260930, 'suites': {}}
    pairs = masks = words = 0
    for m in range(1, 5):
        for length in range(7):
            for letters in product('ab', repeat=length):
                target = ''.join(letters)
                got, n_masks = literal_singleton_degrees(m, target)
                beta = gap_vector(target)
                expected = {}
                for delta in compositions(m, len(beta)):
                    c = tuple(b + d for b, d in zip(beta, delta))
                    expected[literal_word(c)] = sum(d > 0 for d in delta)
                require(got == expected, ('literal-mask mismatch', m, target))
                pairs += 1
                masks += n_masks
                words += len(got)
    report['suites']['literal_masks'] = dict(source_pairs=pairs, masks=masks,
                                           distinct_word_queries=words)
    print('Literal masks:', report['suites']['literal_masks'], flush=True)
    centers = queries = 0
    for m in range(3, 6):
        for g in range(1, 5):
            for T in range(m, 17):
                for v in partitions(T, g):
                    got, witness, inspected = full_output_test(v, m)
                    require(got == feasible(v, m), ('full output mismatch', m, v, witness))
                    centers += 1
                    queries += inspected
    report['suites']['exhaustive_center_orbits'] = dict(
        m='3..5', g='1..4', T='m..16', center_orbits=centers,
        output_queries_until_first_failure=queries)
    print('Full-output center comparison:', centers, queries, flush=True)
    rng = random.Random(20260930)
    centers = deficits = 0
    for m in range(3, 7):
        for g in range(m, m + 3):
            cases = [tuple(rng.randrange(0, 3 * m + 1) for _ in range(g))
                     for _ in range(40)]
            cases += [canonical_center(m, g, minimum_total(m, g) + d)
                      for d in range(8)]
            cases += [(m,) * g]
            for v in cases:
                got, witness, inspected = deletion_test(v, m)
                require(got == feasible(v, m), ('deficit mismatch', m, v, witness))
                if witness is not None:
                    choices = []
                    for j, x in enumerate(witness):
                        if x >= m:
                            beta = witness[:j] + (x - m,) + witness[j + 1:]
                            choices.append(beta)
                    require(len(choices) == 1, ('witness not unique', m, v, witness))
                    require(not admissible(choices[0], v, m), ('witness accepted', m, v))
                centers += 1
                deficits += inspected
    report['suites']['sampled_local_obstructions'] = dict(
        m='3..6', g='m..m+2', random_centers_per_pair=40,
        constructed_centers_per_pair=9, centers=centers,
        deficit_queries_until_first_failure=deficits)
    print('Local obstruction comparison:', centers, deficits, flush=True)
    example_rows = []
    centers_by_m = {}
    for m in range(3, 7):
        T = minimum_total(m, m)
        vs = [v for v in partitions(T, m, 1) if feasible(v, m)]
        centers_by_m[str(m)] = [list(v) for v in vs]
        if m <= 5:
            for v in vs:
                success, witness, inspected = full_output_test(v, m)
                require(success, ('extremal construction failed', m, v, witness))
                example_rows.append(dict(kind='extremal', m=m, g=m, T=T,
                    center=';'.join(map(str, v)), outputs=inspected,
                    maximal_targets=sum(1 for _ in maximal_targets(v, m))))
    for m in range(3, 6):
        v = (m,) * (m + 1)
        success, witness, inspected = full_output_test(v, m)
        require(success, ('boundary construction failed', m, witness))
        example_rows.append(dict(kind='boundary', m=m, g=m+1, T=sum(v),
            center=';'.join(map(str, v)), outputs=inspected,
            maximal_targets=sum(1 for _ in maximal_targets(v, m))))
    report['suites']['complete_examples'] = example_rows
    print('Complete explicit examples:', example_rows, flush=True)
    count_rows = []
    for m in range(2, 13):
        value = extremal_count(m)
        orbit_count = None
        if 3 <= m <= 7:
            direct = orbit_count = 0
            for v in partitions(minimum_total(m, m), m, 1):
                if feasible(v, m):
                    orbit_count += 1
                    weight = factorial(m)
                    for multiplicity in Counter(v).values():
                        weight //= factorial(multiplicity)
                    direct += weight
            require(direct == value, ('count mismatch', m, direct, value))
        count_rows.append(dict(m=m, minimum_length=minimum_length(m),
            ordered_centers=value, permutation_orbits=orbit_count))
    report['suites']['center_count_orbit_comparison'] = 'm=3..7'
    report['center_counts'] = count_rows
    print('Extremal center counts:', count_rows, flush=True)
    count_cases = 0
    for parts in range(6):
        for cap in range(1, 7):
            direct = Counter(map(sum, product(range(1, cap + 1), repeat=parts)))
            for total in range(parts * cap + 3):
                require(bounded_positive(total, parts, cap) == direct[total],
                        ('bounded composition mismatch', total, parts, cap))
                count_cases += 1
    report['suites']['bounded_composition_counts'] = dict(cases=count_cases)
    parameters = 0
    for m in range(3, 61):
        for g in range(m, m + 31):
            for increment in (0, 1, m, m * m):
                T = minimum_total(m, g) + increment
                require(feasible(canonical_center(m, g, T), m),
                        ('threshold construction mismatch', m, g, T))
                parameters += 1
    report['suites']['parameter_construction'] = dict(
        m='3..60', g='m..m+30', increments=[0,1,'m','m^2'], triples=parameters)
    got, _ = literal_singleton_degrees(2, 'b')
    require(got == {'aab': 1, 'aba': 2, 'baa': 1}, ('m=2', got))
    # Mandatory target classification: compare the explicit transfer rule with
    # the independent singleton-hyperedge criterion on every small extremal type.
    mandatory_rows = []
    for m in range(3, 6):
        for vv in centers_by_m[str(m)]:
            v = tuple(vv)
            E = set(maximal_targets(v, m))
            direct = {tuple(x - 1 for x in v)}
            edges = []
            for c in compositions(sum(v), m):
                if c == v:
                    continue
                edge = set(predecessors(c, m)) & E
                require(edge, ('uncovered center audit', m, c))
                edges.append((c, edge))
                if len(edge) == 1:
                    direct |= edge
            classified = {b for b in E if mandatory_extremal_target(b, v, m)}
            require(classified == direct, ('mandatory mismatch', m, v))
            mandatory_rows.append(dict(m=m, center=list(v),
                                       maximal=len(E), mandatory=len(direct)))
            if m == 3:
                remaining = [(c, edge) for c, edge in edges if not edge & direct]
                require(len(direct) == 28 and len(remaining) == 9,
                        ('degree-three matching sizes', len(direct), len(remaining)))
                optional = set().union(*(edge for _, edge in remaining))
                require(len(optional) == 18 and all(len(edge) == 2 for _, edge in remaining),
                        'degree-three edges must be a disjoint matching')
                require(direct | optional == E, 'degree-three maximal language partition')
                # Exhaust all three nonempty selections on each disjoint pair.
                sorted_pairs = [tuple(sorted(edge)) for _, edge in remaining]
                histogram = Counter()
                for choices in product(range(3), repeat=9):
                    selected = set(direct)
                    for choice, pair in zip(choices, sorted_pairs):
                        selected.update(pair if choice == 2 else (pair[choice],))
                    require(all(edge & selected for _, edge in edges),
                            'matching family does not cover all outputs')
                    histogram[len(selected)] += 1
                require(sum(histogram.values()) == 3**9 and histogram[37] == 2**9,
                        ('degree-three language counts', histogram))
                selected = direct | {pair[0] for pair in sorted_pairs}
                literal_degrees = {}
                mask_count = 0
                for beta in selected:
                    values, used = literal_singleton_degrees(3, literal_word(beta))
                    mask_count += used
                    for w, degree in values.items():
                        literal_degrees[w] = min(literal_degrees.get(w, degree), degree)
                expected = {literal_word(c): 3 if c == v else 1
                            for c in compositions(12, 3)}
                require(literal_degrees == expected, '37-target literal mask audit')
                with (out / 'minimal_degree3_targets.csv').open('w', newline='') as f:
                    writer = csv.writer(f)
                    writer.writerow(['gap_vector', 'target_word', 'mandatory'])
                    for b in sorted(selected):
                        writer.writerow([';'.join(map(str,b)), literal_word(b), b in direct])
                report['degree3_languages'] = dict(mandatory=28, optional_pairs=9,
                    total_languages=3**9, minimal_size=37, minimal_languages=2**9,
                    size_histogram=dict(sorted(histogram.items())),
                    all_languages_checked=3**9, minimal_example_literal_masks=mask_count)
                (out / 'degree3_pair_constraints.json').write_text(json.dumps(
                    [dict(output=list(c), pair=[list(b) for b in sorted(edge)])
                     for c, edge in remaining], indent=2) + '\n')
    report['suites']['mandatory_targets'] = mandatory_rows
    print('Mandatory targets:', mandatory_rows, flush=True)
    print('Degree-three target languages:', report['degree3_languages'], flush=True)
    report['status'] = 'PASS' 
    (out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (out / 'extremal_orbits_m3_m6.json').write_text(json.dumps(centers_by_m, indent=2)+'\n')
    for name, rows in [('extremal_center_counts.csv', count_rows),
                       ('complete_examples.csv', example_rows)]:
        with (out / name).open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)
    print('PASS. Evidence directory:', out, flush=True)


if __name__ == '__main__':
    main()
