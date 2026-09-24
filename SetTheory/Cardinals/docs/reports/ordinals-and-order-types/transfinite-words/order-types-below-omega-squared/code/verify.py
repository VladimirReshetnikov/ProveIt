#!/usr/bin/env python3
"""Reproducible finite checks for the symbolic lemmas in article.tex.

These checks are not a proof of an ordinal maximal-order-type formula. They
compare exact symbolic embedding decisions, never truncations of omega blocks.
Run from any directory: python3 code/verify.py
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
import random
from collections import Counter
from itertools import product
from pathlib import Path
from time import perf_counter
from omega2 import (FinitePoset, Word, all_words, atom_alphabet, embeds,
                    embeds_reference, encode_product, full_marker_map, letter,
                    naturally_labelled_posets, normalize, omega, ordinal_length,
                    pad_to_limit, proper_marker_map, theorem_value)

ROOT = Path(__file__).resolve().parents[1]
SEED = 20260919
COUNTS: Counter[str] = Counter()
RNG = random.Random(SEED)
SAMPLES = 250
PAIR_BOUND = 4
PAIR_TOTALS: dict[str, dict[str, int]] = {}


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


def exhaustive_pair_checks(p: FinitePoset, bound: int, name: str) -> None:
    """Every ordered pair of token expressions over a binary alphabet.

    Checks greedy/reference agreement, that normalization preserves both the
    equivalence class and the ordinal length, that it preserves every decided
    relation, and that mutually embeddable expressions have identical normal
    forms. The last assertion is the executable form of Proposition 11.2.
    """
    ws = tuple(all_words(atom_alphabet(p, p.downsets(nonempty=True)), bound))
    normal = {u: normalize(u) for u in ws}
    for u in ws:
        p.validate_word(u)
        require(embeds(p, u, normal[u], validate=False) and
                embeds(p, normal[u], u, validate=False),
                'normalization_equivalence', (p.pred, u))
        require(ordinal_length(u) == ordinal_length(normal[u]),
                'normalization_preserves_length', (p.pred, u))
    for u in ws:
        nu = normal[u]
        for v in ws:
            decided = embeds(p, u, v, validate=False)
            require(decided == embeds_reference(p, u, v),
                    'binary_pair_decider_agreement', (p.pred, u, v))
            require(decided == embeds(p, nu, normal[v], validate=False),
                    'normalization_preserves_relation', (p.pred, u, v))
            if decided and embeds(p, v, u, validate=False):
                require(nu == normal[v], 'canonical_quotient', (p.pred, u, v))
    PAIR_TOTALS[name] = {'word_count': len(ws), 'ordered_pairs': len(ws) ** 2,
                         'max_tokens': bound}


def check_binary_support_families() -> int:
    """Every allowed support subfamily of both two-letter alphabets.

    The exceptional universal-only activation is skipped, exactly as the
    hypotheses of Theorem 6.5 require. Repeated support prefixes occurring in
    different subfamilies are deliberately retested.
    """
    stages = 0
    for p in (FinitePoset.antichain(2), FinitePoset.chain(2)):
        downsets = p.downsets(nonempty=True)
        for mask in range(1 << len(downsets)):
            selected = tuple(d for i, d in enumerate(downsets) if mask & (1 << i))
            old: tuple[int, ...] = ()
            for d in selected:
                if d == p.full and not old:
                    continue
                stages += 1
                pool = tuple(all_words(atom_alphabet(p, old), 1))
                for arity in (1, 2, 3):
                    tuples = tuple(product(pool, repeat=arity))
                    images = tuple(encode_product(p, old, d, us) for us in tuples)
                    for i, us in enumerate(tuples):
                        for j, vs in enumerate(tuples):
                            expected = all(embeds(p, u, v, validate=False)
                                           for u, v in zip(us, vs))
                            require(embeds(p, images[i], images[j],
                                           validate=False) == expected,
                                    'binary_family_product_embedding',
                                    (p.pred, old, d, us, vs))
                old += (d,)
    return stages


def check_fixed_lengths() -> None:
    """Proposition 10.3: a word of length omega*r+k splits as blocks times tail."""
    for n in range(1, 5):
        for p in naturally_labelled_posets(n):
            downsets = p.downsets(nonempty=True)
            letters = atom_alphabet(p, ())
            for _ in range(SAMPLES):
                r, k = RNG.randrange(5), RNG.randrange(5)

                def build() -> tuple[tuple[Word, ...], Word, Word]:
                    blocks = tuple(
                        tuple(RNG.choice(letters) for _ in range(RNG.randrange(7)))
                        + (omega(RNG.choice(downsets)),) for _ in range(r))
                    tail = tuple(letter(RNG.randrange(n)) for _ in range(k))
                    return blocks, tail, tuple(t for b in blocks for t in b) + tail

                ub, ut, u = build()
                vb, vt, v = build()
                require(ordinal_length(u) == (r, k) == ordinal_length(v),
                        'fixed_length_generation', (u, v))
                expected = (all(embeds(p, a, b, validate=False)
                                for a, b in zip(ub, vb)) and
                            embeds(p, ut, vt, validate=False))
                require(embeds(p, u, v, validate=False) == expected,
                        'fixed_length_product', (p.pred, u, v))


def negative_controls() -> dict[str, str]:
    """The three invalid shortcuts of Section 8.4, required to fail."""
    p = FinitePoset.antichain(2)
    a, b = letter(0), letter(1)
    u: Word = (a,)
    v: Word = ()
    full: Word = (omega(p.full),)
    # Shortcut 1: without a guard, a component is absorbed by the separator.
    require(not embeds(p, u, v) and embeds(p, u + full, v + full),
            'negative_control_unguarded_absorption')
    # Shortcut 2: a finite guard does not repair the universal separator.
    require(embeds(p, u + (a,) + full, v + (a,) + full),
            'negative_control_finite_guard_at_full_support')
    # Shortcut 3: a new downset contained in an old one destroys synchronization.
    src = ((), (a,))
    tgt = ((omega(p.full),), ())
    naive = lambda seq: seq[0] + (b, omega(1)) + seq[1] + (b,)
    require(not embeds(p, src[1], tgt[1]),
            'negative_control_old_support_contains_new_support')
    require(embeds(p, naive(src), naive(tgt)),
            'negative_control_old_support_contains_new_support')
    return {'unguarded_absorption': 'detected',
            'finite_guard_at_full_support': 'detected',
            'old_support_contains_new_support': 'detected'}


def check_maximal_elements() -> None:
    """B_{Max D} is equivalent to B_D because Max D generates D."""
    for n in range(1, 5):
        for p in naturally_labelled_posets(n):
            for d in p.downsets(nonempty=True):
                maxima = p.maximal_elements(d)
                generated = 0
                for x in maxima:
                    generated |= p.pred[x]
                require(generated == d, 'maximal_elements_generate', (p.pred, d))


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
    catalogue = []
    for n in range(1, 5):
        for index, p in enumerate(naturally_labelled_posets(n)):
            downsets = p.downsets(nonempty=True)
            catalogue.append({
                'n': n, 'index': index,
                'pred_masks': ';'.join(str(m) for m in p.pred),
                'upper_masks': ';'.join(str(p.upper_mask(x)) for x in range(n)),
                'ideal_count_including_empty': len(downsets) + 1,
                'omega_tower_inner_exponent':
                    n + len(downsets) - 1 if n >= 2 else 'exception: omega^2'})
    with (ROOT / 'data/finite_posets.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(catalogue[0]))
        writer.writeheader()
        writer.writerows(catalogue)
    with (ROOT / 'data/examples.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['poset', 'n', 'j_including_empty', 'maximal_order_type'])
        for name, p in examples:
            writer.writerow([name, p.n, len(p.downsets()), theorem_value(p)])
    return enumeration, len(catalogue)


def main() -> None:
    global SEED, SAMPLES, PAIR_BOUND
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=SEED,
                        help='seed for every pseudorandom check (default 20260919)')
    parser.add_argument('--samples', type=int, default=SAMPLES,
                        help='seeded samples per poset in the fixed-length check')
    parser.add_argument('--pair-bound', type=int, default=PAIR_BOUND,
                        help='token length bound for the exhaustive binary domain')
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'data',
                        help='directory receiving the generated reports and tables')
    args = parser.parse_args()
    if args.samples < 1 or not 0 <= args.pair_bound <= 5:
        parser.error('samples must be positive; pair-bound must lie in [0,5]')
    SEED, SAMPLES, PAIR_BOUND = args.seed, args.samples, args.pair_bound
    RNG.seed(SEED)
    started = perf_counter()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (ROOT / 'data').mkdir(exist_ok=True)
    check_regressions()
    controls = negative_controls()
    print('Regression cases and negative controls passed.', flush=True)
    check_maximal_elements()
    compare_deciders()
    for name, poset in (('antichain_2', FinitePoset.antichain(2)),
                        ('chain_2', FinitePoset.chain(2))):
        exhaustive_pair_checks(poset, PAIR_BOUND, name)
    print('Embedding deciders agree; normal forms are canonical.', flush=True)
    check_product_maps()
    binary_stages = check_binary_support_families()
    print('Product, padding, and support-family embeddings passed.', flush=True)
    check_universal_only()
    check_fixed_lengths()
    enumeration, catalogued = make_tables()
    report = {'status': 'PASS', 'seed': SEED, 'python_version': platform.python_version(),
              'samples_per_stage': SAMPLES, 'exhaustive_pair_bound': PAIR_BOUND,
              'elapsed_seconds': round(perf_counter() - started, 3),
              'checks': dict(sorted(COUNTS.items())),
              'total_assertions': sum(v for k, v in COUNTS.items() if k != 'marker_stages'),
              'exhaustive_binary_domain': PAIR_TOTALS,
              'binary_support_families': {'activation_stages': binary_stages},
              'negative_controls': controls,
              'catalogued_posets': catalogued,
              'naturally_labelled_poset_counts': enumeration,
              'scope': 'Exact symbolic omega-block tests; not finite truncations and not '
                       'a formal verification of the maximal-order-type theorem.'}
    (args.output_dir / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (args.output_dir / 'verification.txt').write_text(
        '\n'.join(f'{k}: {v}' for k, v in report.items()) + '\n')
    (args.output_dir / 'test_summary.tex').write_text(
        f'\\newcommand{{\\TestAssertions}}{{{report["total_assertions"]:,}}}\n'
        f'\\newcommand{{\\ProductChecks}}{{{COUNTS["exhaustive_product_embedding"] + COUNTS["random_product_embedding"] + COUNTS["binary_family_product_embedding"]:,}}}\n'
        f'\\newcommand{{\\MarkerStages}}{{{COUNTS["marker_stages"]:,}}}\n'
        f'\\newcommand{{\\DeciderChecks}}{{{COUNTS["exhaustive_decider_agreement"] + COUNTS["random_decider_agreement"] + COUNTS["binary_pair_decider_agreement"]:,}}}\n'
        f'\\newcommand{{\\BinaryPairs}}{{{sum(v["ordered_pairs"] for v in PAIR_TOTALS.values()):,}}}\n'
        f'\\newcommand{{\\BinaryStages}}{{{binary_stages:,}}}\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
