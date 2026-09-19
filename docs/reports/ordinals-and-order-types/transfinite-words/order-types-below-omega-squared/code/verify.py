#!/usr/bin/env python3
"""Reproducible finite checks for the symbolic lemmas in article.tex.

These checks are not a proof of an ordinal maximal-order-type formula. They
compare exact symbolic embedding decisions, never truncations of omega blocks.
Run from any directory: python3 code/verify.py
"""
from __future__ import annotations
import csv
import json
import platform
import random
from collections import Counter
from itertools import product
from pathlib import Path
from time import perf_counter
from omega2 import (FinitePoset, Word, all_words, atom_alphabet, embeds,
                    embeds_reference, full_marker_map, letter,
                    naturally_labelled_posets, omega, ordinal_length,
                    pad_to_limit, proper_marker_map, theorem_value)

ROOT = Path(__file__).resolve().parents[1]
SEED = 20260919
COUNTS: Counter[str] = Counter()
RNG = random.Random(SEED)


def require(condition: bool, label: str, context: object = None) -> None:
    COUNTS[label] += 1
    if not condition:
        raise AssertionError(f'{label}: {context!r}')


def compare_deciders() -> None:
    # Every naturally labelled poset with <=3 elements, all code words <=2.
    for n in range(4):
        for p in naturally_labelled_posets(n):
            words = tuple(all_words(atom_alphabet(p, p.downsets(nonempty=True)), 2))
            for u, v in product(words, repeat=2):
                require(embeds(p, u, v, validate=False) == embeds_reference(p, u, v),
                        'exhaustive_decider_agreement', (p.pred, u, v))
    # Longer exact symbolic words, including every naturally labelled 4-poset.
    for n in range(2, 5):
        for p in naturally_labelled_posets(n):
            atoms = atom_alphabet(p, p.downsets(nonempty=True))
            for _ in range(200):
                u = tuple(RNG.choice(atoms) for _ in range(RNG.randrange(13)))
                v = tuple(RNG.choice(atoms) for _ in range(RNG.randrange(13)))
                require(embeds(p, u, v, validate=False) == embeds_reference(p, u, v),
                        'random_decider_agreement', (p.pred, u, v))


def check_product_maps() -> None:
    for n in range(2, 5):
        for p in naturally_labelled_posets(n):
            old: list[int] = []
            for d in p.downsets(nonempty=True):
                atoms = atom_alphabet(p, old)
                # A deterministic pool, with previously introduced omega tokens.
                pool: tuple[Word, ...] = ((), (letter(0),),
                    (omega(old[-1]),) if old else (letter(n - 1),),
                    (letter(n - 1),) + ((omega(old[0]),) if old else ()) + (letter(0),))
                if d == p.full:
                    e = next(x for x in old if x != p.full)
                    transform = lambda us: full_marker_map(p, e, us)
                else:
                    transform = lambda us: proper_marker_map(p, d, us)
                for arity in (2, 3):
                    tuples = tuple(product(pool, repeat=arity))
                    images = tuple(transform(us) for us in tuples)
                    for i, us in enumerate(tuples):
                        for j, vs in enumerate(tuples):
                            expected = all(embeds(p, u, v, validate=False)
                                           for u, v in zip(us, vs))
                            got = embeds(p, images[i], images[j], validate=False)
                            require(got == expected, 'exhaustive_product_embedding',
                                    (p.pred, d, us, vs, got, expected))
                for _ in range(100):
                    arity = RNG.randrange(2, 6)
                    us = tuple(tuple(RNG.choice(atoms) for _ in range(RNG.randrange(9)))
                               for _ in range(arity))
                    vs = tuple(tuple(RNG.choice(atoms) for _ in range(RNG.randrange(9)))
                               for _ in range(arity))
                    require(embeds(p, transform(us), transform(vs), validate=False) ==
                            all(embeds(p, u, v, validate=False) for u, v in zip(us, vs)),
                            'random_product_embedding', (p.pred, d, us, vs))
                COUNTS['marker_stages'] += 1
                old.append(d)
            # Test padding independently using all one-token words as components.
            for e in p.downsets(nonempty=True):
                if e == p.full:
                    continue
                pool = tuple(all_words(atom_alphabet(p, p.downsets(nonempty=True)), 1))
                for u in pool:
                    gu = pad_to_limit(p, u, e)
                    k, m = ordinal_length(gu)
                    require(k > 0 and m == 0, 'padding_limit_length', (p.pred, e, u))
                    for v in pool:
                        require(embeds(p, gu, pad_to_limit(p, v, e), validate=False) ==
                                embeds(p, u, v, validate=False),
                                'padding_order_embedding', (p.pred, e, u, v))


def check_universal_only() -> None:
    for n in range(1, 4):
        for p in naturally_labelled_posets(n):
            us = tuple(all_words(atom_alphabet(p, ()), 2))
            for k, l in product(range(4), repeat=2):
                for u, v in product(us, repeat=2):
                    source = (omega(p.full),) * k + u
                    target = (omega(p.full),) * l + v
                    expected = k < l or (k == l and embeds(p, u, v, validate=False))
                    require(embeds(p, source, target, validate=False) == expected,
                            'universal_only_normal_form', (p.pred, k, l, u, v))
            for code in all_words(atom_alphabet(p, (p.full,)), 4):
                k = sum(tag == 'w' for tag, _ in code)
                last = max((i for i, t in enumerate(code) if t[0] == 'w'), default=-1)
                normal = (omega(p.full),) * k + code[last + 1:]
                require(embeds(p, code, normal, validate=False) and
                        embeds(p, normal, code, validate=False),
                        'universal_only_normalization', (p.pred, code, normal))


def check_regressions() -> None:
    p = FinitePoset.antichain(2)
    a, b, A, B, U = letter(0), letter(1), omega(1), omega(2), omega(3)
    cases = [((a, A), (A,), True), ((A,), (a, A), True),
             ((A, a), (A,), False), ((A, B), (U,), False),
             ((U,), (A, B), False), ((A,), (U,), True),
             ((b, A), (A,), False), ((), (), True),
             ((U,), (U, a), True), ((U, a), (U,), False)]
    for u, v, expected in cases:
        require(embeds(p, u, v) == expected, 'regression_cases', (u, v))
    # Naive finite padding cannot force the universal marker to reflect products:
    # a U == U. Limit padding is essential, not cosmetic.
    require(embeds(p, (a, U), (U,)), 'finite_padding_counterexample')
    require(not embeds(p, (a, b, A, U), (b, A, U)),
            'limit_padding_blocks_absorption')
    require(theorem_value(FinitePoset(())) == '1', 'boundary_values')
    require(theorem_value(FinitePoset.chain(1)) == 'omega^2', 'boundary_values')
    require(theorem_value(FinitePoset.chain(2)) == 'omega^(omega^3)', 'boundary_values')
    require(theorem_value(p) == 'omega^(omega^4)', 'boundary_values')


def make_tables() -> dict[str, int]:
    enumeration = {}
    rows = []
    for n in range(6):
        ps = tuple(naturally_labelled_posets(n))
        enumeration[str(n)] = len(ps)
        histogram = Counter(len(p.downsets()) for p in ps)
        for j, count in sorted(histogram.items()):
            rows.append({'n': n, 'number_of_downsets_including_empty': j,
                         'natural_label_relations_count': count,
                         'exponent_parameter': n + j - 2 if n >= 2 else '',
                         'maximal_order_type': ('1' if n == 0 else 'omega^2') if n < 2
                         else f'omega^(omega^{n + j - 2})'})
    with (ROOT / 'data/ideal_counts.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    examples = [('empty', FinitePoset(())), ('singleton', FinitePoset.chain(1))]
    for n in range(2, 6):
        examples += [(f'chain_{n}', FinitePoset.chain(n)),
                     (f'antichain_{n}', FinitePoset.antichain(n))]
    examples += [('V_3', FinitePoset.from_covers(3, [(0, 1), (0, 2)])),
                 ('dual_V_3', FinitePoset.from_covers(3, [(0, 2), (1, 2)])),
                 ('chain_2_plus_isolated', FinitePoset.from_covers(3, [(0, 1)])),
                 ('diamond_4', FinitePoset.from_covers(4, [(0, 1), (0, 2), (1, 3), (2, 3)]))]
    with (ROOT / 'data/examples.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['poset', 'n', 'j_including_empty', 'maximal_order_type'])
        for name, p in examples:
            writer.writerow([name, p.n, len(p.downsets()), theorem_value(p)])
    return enumeration


def main() -> None:
    started = perf_counter()
    (ROOT / 'data').mkdir(exist_ok=True)
    check_regressions()
    compare_deciders()
    print('Embedding deciders agree.', flush=True)
    check_product_maps()
    print('Product and padding embeddings passed.', flush=True)
    check_universal_only()
    enumeration = make_tables()
    report = {'status': 'PASS', 'seed': SEED, 'python_version': platform.python_version(),
              'elapsed_seconds': round(perf_counter() - started, 3),
              'checks': dict(sorted(COUNTS.items())),
              'total_assertions': sum(v for k, v in COUNTS.items() if k != 'marker_stages'),
              'naturally_labelled_poset_counts': enumeration,
              'scope': 'Exact symbolic omega-block tests; not finite truncations and not '
                       'a formal verification of the maximal-order-type theorem.'}
    (ROOT / 'data/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (ROOT / 'data/verification.txt').write_text(
        '\n'.join(f'{k}: {v}' for k, v in report.items()) + '\n')
    (ROOT / 'data/test_summary.tex').write_text(
        f'\\newcommand{{\\TestAssertions}}{{{report["total_assertions"]:,}}}\n'
        f'\\newcommand{{\\ProductChecks}}{{{COUNTS["exhaustive_product_embedding"] + COUNTS["random_product_embedding"]:,}}}\n'
        f'\\newcommand{{\\MarkerStages}}{{{COUNTS["marker_stages"]:,}}}\n'
        f'\\newcommand{{\\DeciderChecks}}{{{COUNTS["exhaustive_decider_agreement"] + COUNTS["random_decider_agreement"]:,}}}\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
