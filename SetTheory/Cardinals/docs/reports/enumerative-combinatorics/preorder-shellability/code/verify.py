#!/usr/bin/env python3
"""Exact tests of the base-block shelling of finite integral polymatroids.

Standard library only. Run from the package root:
    python3 code/verify.py --output results
No random sampling and no floating-point mathematics are used.
"""
from __future__ import annotations
import argparse
import csv
import itertools
import json
import math
import platform
import sys
from collections import Counter
from pathlib import Path
from typing import Iterable, Iterator, Sequence

Vector = tuple[int, ...]

def weak_compositions(total: int, length: int) -> Iterator[Vector]:
    if length == 0:
        if total == 0:
            yield ()
        return
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in weak_compositions(total - first, length - 1):
            yield (first,) + tail

def leq(a: Vector, b: Vector) -> bool:
    return all(x <= y for x, y in zip(a, b))

def transfer(b: Vector, i: int, j: int) -> Vector:
    v = list(b)
    v[i] += 1
    v[j] -= 1
    return tuple(v)

def preorders(n: int) -> Iterator[tuple[int, tuple[int, ...]]]:
    """Every labeled reflexive transitive relation, once; rows encode upsets."""
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for mask in range(1 << len(pairs)):
        rows = [1 << i for i in range(n)]
        for bit, (i, j) in enumerate(pairs):
            if mask & (1 << bit):
                rows[i] |= 1 << j
        if all(not (rows[i] & (1 << j)) or rows[j] & ~rows[i] == 0
               for i in range(n) for j in range(n)):
            yield mask, tuple(rows)

def ideal_masks(rows: Sequence[int]) -> list[int]:
    n = len(rows)
    return [m for m in range(1 << n)
            if all(not (rows[i] & m) or m & (1 << i) for i in range(n))]

def lattice_points(rows: Sequence[int], capacities: Vector | None = None) -> set[Vector]:
    """Independent enumeration using exactly the source's ideal inequalities."""
    n = len(rows)
    c = (1,) * n if capacities is None else capacities
    if len(c) != n or any(x < 0 for x in c):
        raise ValueError('Invalid capacities')
    ideals = [[i for i in range(n) if m & (1 << i)] for m in ideal_masks(rows)]
    constraints = [(I, sum(c[i] for i in I)) for I in ideals]
    return {a for t in range(sum(c) + 1) for a in weak_compositions(t, n)
            if all(sum(a[i] for i in I) <= bound for I, bound in constraints)}

def assigned_bases(rows: Sequence[int], capacities: Vector | None = None) -> set[Vector]:
    """Independent complete token assignments, with labeled supply copies."""
    n = len(rows)
    c = (1,) * n if capacities is None else capacities
    choices = [[j for j in range(n) if rows[i] & (1 << j)]
               for i in range(n) for _ in range(c[i])]
    return {tuple(word.count(i) for i in range(n)) for word in itertools.product(*choices)}

def base_exchange(bases: set[Vector]) -> bool:
    """Specified insertion exchange; checks every ordered pair and deficit."""
    for b in bases:
        for c in bases:
            for i, (bi, ci) in enumerate(zip(b, c)):
                if bi < ci and not any(bj > cj and transfer(b, i, j) in bases
                                       for j, (bj, cj) in enumerate(zip(b, c))):
                    return False
    return True

def active_set(b: Vector, bases: set[Vector]) -> set[int]:
    return {j for j in range(len(b)) if b[j] and any(
        transfer(b, i, j) in bases for i in range(j))}

def content_words(b: Vector, order: Sequence[int]) -> Iterator[tuple[int, ...]]:
    remaining = list(b)
    prefix: list[int] = []
    def rec() -> Iterator[tuple[int, ...]]:
        if len(prefix) == sum(b):
            yield tuple(prefix)
            return
        for j in order:
            if remaining[j]:
                remaining[j] -= 1
                prefix.append(j)
                yield from rec()
                prefix.pop()
                remaining[j] += 1
    yield from rec()

def chain(word: Sequence[int], n: int) -> tuple[Vector, ...]:
    a = [0] * n
    out = []
    for j in word:
        a[j] += 1
        out.append(tuple(a))
    return tuple(out)

def all_subsets(vertices: Sequence[Vector]) -> list[frozenset[Vector]]:
    return [frozenset(vertices[i] for i in range(len(vertices)) if mask & (1 << i))
            for mask in range(1 << len(vertices))]

def check_shelling(bases: set[Vector], check_exchange: bool = True,
                   keep_facets: bool = False) -> dict:
    if not bases:
        raise ValueError('A nonempty base family is required')
    n = len(next(iter(bases)))
    r = sum(next(iter(bases)))
    if not all(len(b) == n and sum(b) == r and min(b, default=0) >= 0 for b in bases):
        raise ValueError('Bases must be nonnegative and equidegree')
    if check_exchange:
        assert base_exchange(bases), 'Insertion exchange fails'
    # The face complex is built from actual vertex sets, not overlap formulas.
    seen: set[frozenset[Vector]] = set()
    h_shell = [0] * (r + 1)
    flag_h_shell: Counter[int] = Counter()
    facets = []
    earlier_ideal: set[Vector] = set()
    facet_count = 0
    for b in sorted(bases, reverse=True):
        active = active_set(b, bases)
        order = sorted(range(n), key=lambda j: (j in active, j))
        pos = {j: k for k, j in enumerate(order)}
        box = set(itertools.product(*(range(x + 1) for x in b)))
        predicted_overlap = {a for a in box if any(a[j] < b[j] for j in active)}
        assert box & earlier_ideal == predicted_overlap
        for w in content_words(b, order):
            vertices = chain(w, n)
            F = frozenset(vertices)
            assert len(F) == r
            subfaces = all_subsets(vertices)
            old = [G for G in subfaces if G in seen]
            ridges = [F - {v} for v in F if F - {v} in seen]
            # Definition of pure shelling: every old face lies in an old ridge.
            if facet_count:
                assert ridges, ('No old ridge', b, w)
                assert all(any(G <= R for R in ridges) for G in old), (
                    'Non-pure intersection', b, w)
            else:
                assert not old
            descents = {t for t in range(r - 1) if pos[w[t]] > pos[w[t + 1]]}
            predicted = {vertices[t] for t in descents}
            if r and w[-1] in active:
                predicted.add(vertices[-1])
            # Every new face must contain exactly the proposed restriction face.
            restriction = frozenset(predicted)
            for G in subfaces:
                assert (G not in seen) == (restriction <= G), (
                    'Wrong restriction face', b, w, G)
            h_shell[len(restriction)] += 1
            rank_mask = sum(1 << (sum(a) - 1) for a in restriction)
            flag_h_shell[rank_mask] += 1
            seen.update(subfaces)
            facet_count += 1
            if keep_facets:
                facets.append({'base': b, 'active_1based': sorted(j + 1 for j in active),
                               'alphabet_1based': [j + 1 for j in order],
                               'word_1based': [j + 1 for j in w],
                               'restriction_ranks': [t + 1 for t, a in enumerate(vertices)
                                                     if a in restriction]})
        earlier_ideal |= box
    # Independent face-to-h transform h(t)=sum_F t^|F|(1-t)^(r-|F|).
    f = Counter(map(len, seen))
    h_faces = [0] * (r + 1)
    for size, count in f.items():
        for k in range(r - size + 1):
            h_faces[size + k] += count * math.comb(r - size, k) * (-1) ** k
    assert h_faces == h_shell
    flag_f = Counter(sum(1 << (sum(a) - 1) for a in G) for G in seen)
    for S in range(1 << r):
        flag_h_faces = sum((-1) ** ((S ^ T).bit_count()) * flag_f[T]
                           for T in range(1 << r) if T & ~S == 0)
        assert flag_h_faces == flag_h_shell[S]
    assert facet_count == sum(math.factorial(r) // math.prod(math.factorial(x) for x in b)
                              for b in bases)
    result = {'rank': r, 'coordinates': n, 'bases': len(bases),
              'facets': facet_count, 'faces_including_empty': len(seen),
              'f_by_cardinality': [f[i] for i in range(r + 1)], 'h': h_shell,
              'flag_h_by_rank_mask': [flag_h_shell[S] for S in range(1 << r)]}
    if keep_facets:
        result['facet_order'] = facets
    return result

def naive_order_counterexample() -> dict:
    words = [(0, 2), (1, 2), (2, 0), (2, 1)]
    a, b = (frozenset(chain(w, 3)) for w in words[:2])
    assert not a & b
    repaired = check_shelling({(1, 0, 1), (0, 1, 1)}, keep_facets=True)
    return {'naive_words': [[i+1 for i in w] for w in words],
            'first_two_facets_disjoint': True, 'repaired': repaired}

def write_worked_table(example: dict, path: Path) -> None:
    """Produce the complete LaTeX tabular used by the worked example."""
    def math_set(values: Sequence[int]) -> str:
        return (r'$\{' + ','.join(map(str, values)) + r'\}$'
                if values else r'$\varnothing$')
    lines = [r'\begin{tabular}{@{}rccccc@{}}', r'\toprule',
             r'Step & Base & $R(b)$ & Alphabet & Word & Restriction ranks \\',
             r'\midrule']
    for k, row in enumerate(example['facet_order'], 1):
        base = '$' + ''.join(map(str, row['base'])) + '$'
        active = math_set(row['active_1based'])
        alphabet = '$' + r'\prec '.join(map(str, row['alphabet_1based'])) + '$'
        word = '$' + ''.join(map(str, row['word_1based'])) + '$'
        restriction = math_set(row['restriction_ranks'])
        lines.append(f'{k} & {base} & {active} & {alphabet} & {word} & {restriction}'
                     + r' \\')
    lines.extend([r'\bottomrule', r'\end{tabular}'])
    path.write_text('\n'.join(lines) + '\n', encoding='utf-8')

def main() -> None:
    if not __debug__:
        raise RuntimeError("The verifier must run without -O: its checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('results'))
    parser.add_argument('--max-n', type=int, default=4, choices=range(1, 6))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    rows_out = []
    totals = []
    samples = {}
    for n in range(1, args.max_n + 1):
        count = facet_total = face_total = 0
        for relation_mask, rows in preorders(n):
            P = lattice_points(rows)
            bases = {a for a in P if sum(a) == n}
            assert bases == assigned_bases(rows)
            assert all(any(leq(a, b) for b in bases) for a in P)
            result = check_shelling(bases)
            assert result['h'][-1] == 0  # Independent contractibility consequence.
            assert result['faces_including_empty'] >= len(P)
            count += 1
            facet_total += result['facets']
            face_total += result['faces_including_empty']
            rows_out.append({'n': n, 'relation_mask': relation_mask,
                             'points': len(P), 'bases': len(bases),
                             'facets': result['facets'], 'faces': result['faces_including_empty'],
                             'h': json.dumps(result['h'])})
            if n <= 3:
                samples[f'n{n}_mask{relation_mask}'] = {'upset_rows': rows, **result}
        totals.append({'n': n, 'preorders': count, 'facets_checked': facet_total,
                       'faces_counted_with_repetition_between_preorders': face_total})
        print(totals[-1], flush=True)
    # All equidegree base subfamilies in three coordinates, ranks 1, 2, 3.
    polymatroid_totals = []
    for r in range(1, 4):
        comp = list(weak_compositions(r, 3))
        tested = valid = facets = 0
        for mask in range(1, 1 << len(comp)):
            B = {b for i, b in enumerate(comp) if mask & (1 << i)}
            tested += 1
            if base_exchange(B):
                valid += 1
                facets += check_shelling(B, check_exchange=False)['facets']
        polymatroid_totals.append({'rank': r, 'coordinates': 3,
                                  'base_families_tested': tested,
                                  'exchange_families': valid, 'facets_checked': facets})
        print(polymatroid_totals[-1], flush=True)
    weighted = []
    for mask, rows in preorders(3):
        for c in ((2, 1, 1), (0, 2, 2)):
            P = lattice_points(rows, c)
            B = {a for a in P if sum(a) == sum(c)}
            assert B == assigned_bases(rows, c)
            result = check_shelling(B)
            weighted.append({'relation_mask': mask, 'capacities': c, **result})
    example_rows = (7, 2, 4)  # 1<2 and 1<3: no maximum.
    example_B = assigned_bases(example_rows)
    example = {'description': 'Three-element V: 1<2 and 1<3',
               'points': sorted(lattice_points(example_rows)),
               **check_shelling(example_B, keep_facets=True)}
    empty = check_shelling({()})
    assert empty['rank'] == 0 and empty['h'] == [1]
    assert lattice_points(()) == {()} and assigned_bases(()) == {()}
    summary = {'status': 'ALL EXACT CHECKS PASSED', 'preorders': totals,
               'abstract_exchange_families': polymatroid_totals,
               'weighted_preorder_cases': len(weighted),
               'weighted_facets_checked': sum(x['facets'] for x in weighted),
               'checks': ['ideal inequalities versus supply assignments',
                          'equidegree bases and insertion exchange',
                          'base overlap formula',
                          'pure codimension-one shelling intersections',
                          'restriction face for every subface',
                          'face-vector versus descent h-polynomial',
                          'flag face-vector versus restriction-rank flag h-vector',
                          'preorder top h coefficient vanishes'],
               'empty_preorder': {'P': [[]], 'DeltaP': 'one vertex',
                                  'DeltaPminus0': 'empty-face complex'}}
    (args.output / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    (args.output / 'small_examples.json').write_text(json.dumps(samples, indent=2) + '\n')
    (args.output / 'weighted_cases.json').write_text(json.dumps(weighted, indent=2) + '\n')
    (args.output / 'worked_example.json').write_text(json.dumps(example, indent=2) + '\n')
    (args.output / 'naive_lex_counterexample.json').write_text(
        json.dumps(naive_order_counterexample(), indent=2) + '\n')
    with (args.output / 'preorders.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=rows_out[0].keys())
        writer.writeheader()
        writer.writerows(rows_out)
    write_worked_table(example, args.output / 'worked_table.tex')
    (args.output / 'run.txt').write_text(
        '\n'.join(str(row) for row in totals + polymatroid_totals) + '\n'
        + json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    environment = {'python_version': sys.version, 'implementation': platform.python_implementation(),
                   'platform': platform.platform(), 'optimized': not __debug__,
                   'external_python_dependencies': [], 'max_n': args.max_n}
    (args.output / 'environment.json').write_text(json.dumps(environment, indent=2) + '\n')
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    main()
