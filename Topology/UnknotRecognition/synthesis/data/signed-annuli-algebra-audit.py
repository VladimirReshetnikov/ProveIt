#!/usr/bin/env python3
"""Independent, explicit audit of fastunknot.cyclic_basis.

The decision oracle enumerates all 16 rank-two type-II Whitehead maps and
strictly minimizes the total cyclic length.  It does not use exponent sums,
determinants, the producer's Euclidean algorithm, or WordArena.  Every literal
word/pair within the stated finite bounds is checked; caching only identifies
cyclic rotations, independent inversions, and permutation of tuple entries.

The compiler audit compares its backwards SLP compilation with direct forward
literal substitutions, including the unreduced words.  These checks are finite
regression evidence, not a proof or an asymptotic performance benchmark.
"""

import argparse
from collections import Counter
import copy
from functools import lru_cache
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import random
import sys
import time


ALPHABET = (-2, -1, 1, 2)


def inverse(word):
    return tuple(-x for x in reversed(word))


def reduce_word(word):
    stack = []
    for x in word:
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
    return tuple(stack)


def cyclic_reduce(word):
    word = reduce_word(word)
    a, b = 0, len(word)
    while a + 1 < b and word[a] == -word[b - 1]:
        a += 1
        b -= 1
    return word[a:b]


def cyclic_key(word):
    word = cyclic_reduce(word)
    if not word:
        return ()
    rev = inverse(word)
    return min(*(word[i:] + word[:i] for i in range(len(word))),
               *(rev[i:] + rev[:i] for i in range(len(rev))))


def tuple_key(words):
    return tuple(sorted(cyclic_key(word) for word in words))


def whitehead_maps():
    maps = []
    for multiplier in ALPHABET:
        other = [x for x in ALPHABET if abs(x) != abs(multiplier)]
        for flags in itertools.product((False, True), repeat=2):
            subset = {multiplier} | {x for x, yes in zip(other, flags) if yes}
            images = {}
            for x in (1, 2):
                if abs(x) == abs(multiplier):
                    image = (x,)
                else:
                    image = ((-multiplier,) if -x in subset else ())
                    image += (x,)
                    image += (multiplier,) if x in subset else ()
                images[x] = image
                images[-x] = inverse(image)
            maps.append(images)
    assert len(maps) == 16
    return maps


WHITEHEAD = whitehead_maps()


def substitute(word, images):
    return tuple(letter for x in word for letter in images[x])


@lru_cache(maxsize=None)
def minimize_key(words):
    length = sum(map(len, words))
    best = words
    best_length = length
    for images in WHITEHEAD:
        candidate = tuple_key(substitute(word, images) for word in words)
        candidate_length = sum(map(len, candidate))
        if candidate_length < best_length:
            best = candidate
            best_length = candidate_length
    if best_length == length:
        return words
    return minimize_key(best)


def oracle(words):
    minimal = minimize_key(tuple_key(words))
    return (all(len(word) == 1 for word in minimal) and
            len({abs(word[0]) for word in minimal}) == len(minimal))


def cyclic_words(max_length):
    result = {0: [()]}
    reduced = [()]
    for length in range(1, max_length + 1):
        reduced = [word + (x,) for word in reduced for x in ALPHABET
                   if not word or word[-1] != -x]
        result[length] = [word for word in reduced
                          if length == 1 or word[0] != -word[-1]]
    return result


def move_images(generators, move):
    images = {g: (g,) for g in generators}
    if move['kind'] == 'invert':
        images[move['generator']] = (-move['generator'],)
    elif move['kind'] == 'swap':
        a, b = move['first'], move['second']
        images[a], images[b] = (b,), (a,)
    else:
        a, b, k = move['target'], move['donor'], move['exponent']
        power = ((b,) if k > 0 else (-b,)) * abs(k)
        images[a] = power + (a,) if move['side'] == 'left' else (a,) + power
    images.update({-g: inverse(images[g]) for g in generators})
    return images


def forward(words, generators, moves, *, reduce_each=False, cap=100000):
    """Literal substitution in chronological order, never producer helpers."""
    words = [tuple(w) for w in words]
    for move in moves:
        images = move_images(generators, move)
        if any(sum(len(images[x]) for x in w) > cap for w in words):
            raise OverflowError('explicit audit cap')
        words = [substitute(w, images) for w in words]
        if reduce_each:
            words = [reduce_word(w) for w in words]
    return words


def inverse_moves(moves):
    result = []
    for move in reversed(moves):
        step = dict(move)
        if step['kind'] == 'multiply':
            step['exponent'] = -step['exponent']
        result.append(step)
    return result


def random_move(rng, generators):
    kind = rng.choice(('invert', 'swap', 'multiply', 'multiply', 'multiply'))
    if kind == 'invert':
        return dict(kind=kind, generator=rng.choice(generators))
    a, b = rng.sample(generators, 2)
    if kind == 'swap':
        return dict(kind=kind, first=a, second=b)
    return dict(kind=kind, target=a, donor=b,
                exponent=rng.choice((-7, -5, -3, -2, -1, 1, 2, 3, 5, 7)),
                side=rng.choice(('left', 'right')))


def random_word(rng, generators, length):
    alphabet = generators + [-x for x in generators]
    return tuple(rng.choice(alphabet) for _ in range(length))


def signed_sums(word):
    return (sum(1 if x == 1 else -1 if x == -1 else 0 for x in word),
            sum(1 if x == 2 else -1 if x == -2 else 0 for x in word))


def determinant(words):
    (a, c), (b, d) = map(signed_sums, words)
    return a * d - b * c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    default_fast = Path(__file__).resolve().parents[1] / 'ProveIt/Topology/UnknotRecognition/fast'
    parser.add_argument('--fast-path', type=Path, default=default_fast)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('audit_results.json'))
    parser.add_argument('--single-length', type=int, default=6)
    parser.add_argument('--pair-total-length', type=int, default=6)
    parser.add_argument('--random-cases', type=int, default=400)
    parser.add_argument('--compiler-cases', type=int, default=400)
    parser.add_argument('--seed', type=int, default=20261012)
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_path.resolve()))
    producer = importlib.import_module('fastunknot.cyclic_basis')
    verifier = importlib.import_module('fastunknot.cyclic_basis_verify')
    kernel = importlib.import_module('fastunknot.compressed_words')
    initial_hashes = {Path(module.__file__).name:
                      hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                      for module in (producer, verifier, kernel)}
    start = time.perf_counter()
    counts = Counter()
    reasons = Counter()
    discrepancies = []
    invalid_inputs = []
    certificate_failures = []
    compiler_failures = []
    corruption_failures = []
    corruption_counts = Counter()
    maxima = Counter()
    rng = random.Random(args.seed)

    def check(words, group):
        words = [tuple(w) for w in words]
        expected = oracle(words)
        result = producer.literal_cyclic_basis(words, [1, 2])
        actual = result['status'] == 'COMPLETE'
        counts[group] += 1
        counts[group + '_positive'] += expected
        reasons[result.get('reason', 'COMPLETE')] += 1
        if actual != expected:
            discrepancies.append(dict(group=group, words=words, expected=expected, result=result))
        if actual:
            cert = result['certificate']
            checked = verifier.verify_literal_cyclic_basis(words, [1, 2], cert)
            replay = [cyclic_reduce(w) for w in
                      forward(words, [1, 2], cert['moves'], reduce_each=True)]
            explicit_checked = replay == [(target,) for target in cert['targets']]
            counts['positive_certificates_checked'] += 1
            if not checked or not explicit_checked:
                certificate_failures.append(dict(group=group, words=words,
                                                 verifier=checked, explicit=explicit_checked))

    table = cyclic_words(max(args.single_length, args.pair_total_length - 1))
    for length in range(1, args.single_length + 1):
        for word in table[length]:
            check([word], 'exhaustive_single')
    for total in range(2, args.pair_total_length + 1):
        for first in range(1, total):
            for word1 in table[first]:
                for word2 in table[total - first]:
                    check([word1, word2], 'exhaustive_pair')
    print(json.dumps({'stage': 'exhaustive_done', 'counts': dict(counts)}), flush=True)

    controls = [
        ('primitive_separate_det_two', ((1,), (1, 2, 2))),
        ('primitive_duplicate_det_zero', ((1,), (1,))),
        ('unimodular_one_nonprimitive', ((1, 1, 2, -1, -2), (2,))),
        ('unimodular_both_nonprimitive', ((1, 1, 2, -1, -2), (2, 2, 1, -2, -1))),
        ('independently_conjugated_basis', ((2, 1, -2), (1, 2, -1))),
        ('empty_class', ((), (2,))),
        ('freely_trivial', ((1, -1), (2,))),
        ('rank_bound', ((1,), (2,), (1, 2))),
        ('empty_tuple', ()),
    ]
    control_results = []
    for name, words in controls:
        check(words, 'controls')
        item = dict(name=name, words=words, jointly_primitive=oracle(words),
                    individually_primitive=[oracle([w]) for w in words])
        if len(words) == 2:
            item['determinant'] = determinant(words)
        control_results.append(item)

    for i in range(args.random_cases):
        count = rng.choice((1, 2))
        words = [random_word(rng, [1, 2], rng.randint(1, 40)) for _ in range(count)]
        check(words, 'random_unstructured')
        moves = [random_move(rng, [1, 2]) for _ in range(rng.randint(2, 8))]
        try:
            words = forward([(1,), (2,)][:count], [1, 2], moves,
                            reduce_each=True, cap=1200)
        except OverflowError:
            counts['positive_generation_cap_skips'] += 1
            continue
        wrapped = []
        for word in words:
            conjugator = random_word(rng, [1, 2], rng.randint(0, 8))
            if rng.randrange(2):
                word = inverse(word)
            wrapped.append(conjugator + word + inverse(conjugator))
        assert oracle(wrapped), ('oracle failed generated positive', wrapped, moves)
        check(wrapped, 'random_positive')

    print(json.dumps({'stage': 'decision_done', 'counts': dict(counts)}), flush=True)

    # Fixed noncommuting chronological moves expose an accidental reversal.
    fixed_sequences = [
        [dict(kind='multiply', target=1, donor=2, exponent=3, side='right'),
         dict(kind='multiply', target=2, donor=1, exponent=-2, side='left')],
        [dict(kind='invert', generator=1), dict(kind='swap', first=1, second=2),
         dict(kind='multiply', target=1, donor=2, exponent=-5, side='left'),
         dict(kind='invert', generator=2),
         dict(kind='multiply', target=2, donor=1, exponent=2, side='right')],
    ]
    seq_cases = [([1, 2], seq) for seq in fixed_sequences]
    for _ in range(args.compiler_cases):
        # Nonconsecutive positive labels also exercise alphabet bookkeeping.
        generators = sorted(rng.sample(range(1, 12), rng.randint(2, 5)))
        seq_cases.append((generators, [random_move(rng, generators)
                                      for _ in range(rng.randint(0, 14))]))
    move_kinds = Counter()
    for generators, moves in seq_cases:
        source = [(g,) for g in generators] + [(-g,) for g in generators]
        source += [(), random_word(rng, generators, 12),
                   random_word(rng, generators, 15)]
        try:
            expected = forward(source, generators, moves, cap=40000)
        except OverflowError:
            counts['compiler_generation_cap_skips'] += 1
            continue
        arena = kernel.WordArena(max_nodes=1000000, max_work=10000000)
        roots = [arena.from_word(w) for w in source]
        images = producer.compile_nielsen(arena, generators, moves)
        mapped = producer.map_unreduced(arena, roots, images)
        actual = [tuple(arena.expand(root, limit=40000)) for root in mapped]
        counts['compiler_sequences'] += 1
        counts['compiler_literal_words'] += len(source)
        maxima['compiler_raw_length'] = max(maxima['compiler_raw_length'],
                                            max(map(len, expected)))
        maxima['compiler_moves'] = max(maxima['compiler_moves'], len(moves))
        for move in moves:
            move_kinds[move['kind']] += 1
            if move['kind'] == 'multiply':
                move_kinds[move['side']] += 1
                move_kinds['negative_power' if move['exponent'] < 0 else 'positive_power'] += 1
                move_kinds['power_above_one'] += abs(move['exponent']) > 1
        if actual != expected:
            compiler_failures.append(dict(generators=generators, moves=moves,
                                          source=source, expected=expected, actual=actual))
        else:
            # Inverse automorphism must undo the actual literal images in F_r.
            restored = forward(actual, generators, inverse_moves(moves),
                               reduce_each=True, cap=500000)
            assert [reduce_word(w) for w in restored] == [reduce_word(w) for w in source]
            counts['compiler_inverse_roundtrips'] += len(source)

    # Producer/verifier must agree on each emitted certificate, including
    # out-of-alphabet letters that disappear during free/cyclic reduction.
    for word in ((3,), (3, 1, -3), (3, -3, 1)):
        try:
            result = producer.literal_cyclic_basis([word], [1, 2])
            verified = (result['status'] == 'COMPLETE' and
                        verifier.verify_literal_cyclic_basis([word], [1, 2], result['certificate']))
            item = dict(word=word, outcome=result['status'], verifier=verified)
            if result['status'] == 'COMPLETE' and not verified:
                certificate_failures.append(dict(group='invalid_alphabet', **item))
        except (ValueError, TypeError) as error:
            item = dict(word=word, outcome=type(error).__name__)
        invalid_inputs.append(item)

    # Corruptions split into malformed JSON-schema data (must reject) and
    # syntactically valid changes (accept exactly when the altered proof works).
    # A changed Nielsen list may still be valid: in rank two, switching the
    # side of a shear does not change its action on conjugacy classes.
    corruption_seeds = []
    for words in (((1, 2), (2,)), ((-1, -2), (2,)),
                  ((1, 2, 2, 2, 1, 2, 2),)):
        result = producer.literal_cyclic_basis(words, [1, 2])
        assert result['status'] == 'COMPLETE'
        corruption_seeds.append((list(words), [1, 2], result['certificate']))
    generic_generators = [1, 3, 7]
    generic_moves = [dict(kind='multiply', target=1, donor=3, exponent=3, side='left'),
                     dict(kind='multiply', target=3, donor=7, exponent=-2, side='right'),
                     dict(kind='swap', first=1, second=7),
                     dict(kind='invert', generator=3),
                     dict(kind='multiply', target=7, donor=1, exponent=2, side='right')]
    generic_words = forward([(g,) for g in generic_generators], generic_generators,
                            generic_moves, reduce_each=True)
    generic_certificate = dict(schema='cyclic-basis-nielsen-v1',
                               generators=generic_generators,
                               moves=inverse_moves(generic_moves), targets=generic_generators)
    corruption_seeds.append((generic_words, generic_generators, generic_certificate))

    def check_corruption(words, generators, certificate, label, expected):
        actual = verifier.verify_literal_cyclic_basis(words, generators, certificate)
        corruption_counts[label] += 1
        corruption_counts['accepted' if actual else 'rejected'] += 1
        if actual != expected:
            corruption_failures.append(dict(kind=label, words=words, generators=generators,
                                            certificate=certificate,
                                            expected=expected, actual=actual))

    for words, generators, base in corruption_seeds:
        assert verifier.verify_literal_cyclic_basis(words, generators, base)
        malformed = []
        for field, value in (
                ('schema', 'cyclic-basis-nielsen-v0'),
                ('generators', [float(x) for x in generators]),
                ('generators', [True] + generators[1:]),
                ('targets', [True] + base['targets'][1:]),
                ('targets', [-base['targets'][0]] + base['targets'][1:]),
                ('moves', 'not-a-list')):
            certificate = copy.deepcopy(base)
            certificate[field] = value
            malformed.append(certificate)
        certificate = copy.deepcopy(base)
        certificate['extra'] = 'unrecognized'
        malformed.append(certificate)
        certificate = copy.deepcopy(base)
        del certificate['targets']
        malformed.append(certificate)
        if len(base['targets']) > 1:
            certificate = copy.deepcopy(base)
            certificate['targets'][1] = certificate['targets'][0]
            malformed.append(certificate)
        a, b = generators[:2]
        for move in (
                dict(kind='unknown'),
                dict(kind='invert', generator=True),
                dict(kind='invert', generator=0),
                dict(kind='swap', first=a, second=a),
                dict(kind='multiply', target=a, donor=a, exponent=2, side='left'),
                dict(kind='multiply', target=a, donor=b, exponent=0, side='left'),
                dict(kind='multiply', target=a, donor=b, exponent=True, side='left'),
                dict(kind='multiply', target=a, donor=b, exponent=1.0, side='left'),
                dict(kind='multiply', target=a, donor=b, exponent=2, side='middle')):
            certificate = copy.deepcopy(base)
            certificate['moves'].append(move)
            malformed.append(certificate)
        for certificate in malformed:
            check_corruption(words, generators, certificate, 'malformed_schema', False)

        changed = []
        for moves in (base['moves'][1:], list(reversed(base['moves']))):
            certificate = copy.deepcopy(base)
            certificate['moves'] = moves
            changed.append((words, certificate))
        for index, move in enumerate(base['moves']):
            if move['kind'] == 'multiply':
                for field, value in (('exponent', -move['exponent']),
                                     ('side', 'right' if move['side'] == 'left' else 'left')):
                    certificate = copy.deepcopy(base)
                    certificate['moves'][index][field] = value
                    changed.append((words, certificate))
                break
        certificate = copy.deepcopy(base)
        if len(base['targets']) > 1:
            certificate['targets'] = list(reversed(base['targets']))
        else:
            certificate['targets'] = [next(g for g in generators if g != base['targets'][0])]
        changed.append((words, certificate))
        changed.append(([tuple(words[0]) + (a, b, -a, -b)] + list(words[1:]),
                        copy.deepcopy(base)))
        for altered_words, certificate in changed:
            expected = ([cyclic_reduce(w) for w in forward(
                altered_words, generators, certificate['moves'], reduce_each=True)] ==
                [(g,) for g in certificate['targets']])
            check_corruption(altered_words, generators, certificate,
                             'changed_valid_syntax', expected)

    module_hashes = {}
    for module in (producer, verifier, kernel):
        path = Path(module.__file__)
        module_hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
    changed_modules = [name for name in module_hashes if module_hashes[name] != initial_hashes[name]]
    report = dict(
        audit='independent-rank-two-whitehead-and-nielsen-v1', seed=args.seed,
        bounds=dict(single_cyclic_length=args.single_length,
                    ordered_pair_total_cyclic_length=args.pair_total_length,
                    random_cases=args.random_cases, requested_compiler_cases=args.compiler_cases),
        oracle=dict(type_II_maps=len(WHITEHEAD), cache=minimize_key.cache_info()._asdict(),
                    method='strict total cyclic-length descent; terminal distinct one-letter classes'),
        counts=dict(counts), reasons=dict(reasons), maxima=dict(maxima),
        compiler_move_coverage=dict(move_kinds), controls=control_results,
        invalid_alphabet=invalid_inputs, decision_discrepancies=discrepancies,
        certificate_failures=certificate_failures, compiler_failures=compiler_failures,
        corruption_counts=dict(corruption_counts), corruption_failures=corruption_failures,
        production_sha256=module_hashes,
        production_files_changed_during_run=changed_modules,
        audit_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        elapsed_seconds=round(time.perf_counter() - start, 3),
        passed=not (discrepancies or certificate_failures or compiler_failures or
                    corruption_failures or changed_modules),
        limitations=['Finite explicit regressions do not prove asymptotic complexity.',
                     'No topology, embedding, marking, or native-knot recognition is tested.',
                     'Production verifier shares WordArena; the explicit Whitehead and forward-substitution oracles do not.'])
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
