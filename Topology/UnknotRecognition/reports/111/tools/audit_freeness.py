#!/usr/bin/env python3
"""Independent audit of exact Tietze freeness certificates.

This script is an audit artifact, not a production verifier.  It uses a slow
adjacent-cancellation oracle, tracks explicit maps of every original generator,
and checks original relators in the resulting free group.  It also counts maps
to the nonabelian group S_3 and samples Regina's separate recognizer.
"""

from collections import Counter
from copy import deepcopy
from itertools import product, permutations
from pathlib import Path
import argparse
import hashlib
import json
import random
import sys


def inv(word):
    return tuple(-v for v in reversed(word))


def free(word):
    """Intentionally slow independent rewrite oracle: no production stack."""
    word = tuple(word)
    while True:
        positions = [i for i in range(len(word) - 1) if word[i] == -word[i + 1]]
        if not positions:
            return word
        i = positions[0]
        word = word[:i] + word[i + 2:]


def cyclic(word):
    raw = free(word)
    prefix = ()
    core = raw
    while len(core) > 1 and core[0] == -core[-1]:
        prefix += (core[0],)
        core = core[1:-1]
    assert free(inv(prefix) + raw + prefix) == core
    assert free(prefix + core + inv(prefix)) == raw
    return core


def apply(word, images):
    result = ()
    for x in word:
        result += images[abs(x)] if x > 0 else inv(images[-x])
    return free(result)


def explicit_isomorphism(generators, relators, certificate):
    """Verify legal Tietze changes and both defining inverse-map conditions.

    Every survivor includes as the same generator of the original group.  A
    removed generator is explicitly expressed in the others by its defining
    singleton relation.  The final map is the identity on survivors and sends
    all original relations to the identity in the free group.
    """
    rows = {r['id']: cyclic(r['word']) for r in relators}
    dropped = sorted(r for r in rows if not rows[r])
    rows = {r: w for r, w in rows.items() if w}
    images = {g: (g,) for g in generators}
    alive = set(generators)
    lengths = [sum(map(len, rows.values()))]
    for r, g in certificate['moves']:
        donor = rows.pop(r)
        positions = [i for i, v in enumerate(donor) if abs(v) == g]
        assert len(positions) == 1
        i = positions[0]
        p, q = donor[:i], donor[i + 1:]
        # Derive directly from p g^eps q = 1, without a cyclic rotation.
        value = inv(p) + inv(q) if donor[i] > 0 else q + p
        assert g not in map(abs, value)
        step = {a: (a,) for a in alive}
        step[g] = value
        assert apply(donor, step) == ()
        next_rows = {}
        for name, row in rows.items():
            transformed = cyclic(apply(row, step))
            if transformed:
                next_rows[name] = transformed
            else:
                dropped.append(name)
        images = {a: apply(w, step) for a, w in images.items()}
        alive.remove(g)
        rows = next_rows
        lengths.append(sum(map(len, rows.values())))
        assert lengths[-1] <= lengths[-2]
        assert all(abs(x) in alive for w in images.values() for x in w)
    assert not rows
    assert sorted(alive) == certificate['free_generators']
    assert len(alive) == certificate['free_rank']
    assert sorted(dropped) == certificate['trivial_relators']
    for row in relators:
        assert apply(row['word'], images) == ()
    for g in alive:
        assert images[g] == (g,)
    return images, lengths


S3 = list(permutations(range(3)))
IDENTITY = (0, 1, 2)


def s3_homs(generators, relators):
    count = 0
    for values in product(S3, repeat=len(generators)):
        direct = dict(zip(generators, values))
        assignment = dict(direct)
        for g, perm in direct.items():
            assignment[-g] = tuple(perm.index(i) for i in range(3))
        okay = True
        for row in relators:
            accum = IDENTITY
            for x in row['word']:
                following = assignment[x]
                accum = tuple(accum[following[i]] for i in range(3))
            if accum != IDENTITY:
                okay = False
                break
        count += okay
    return count


def regina_recognize(generators, relators):
    import regina
    label = {g: i for i, g in enumerate(generators)}
    presentation = regina.GroupPresentation(len(generators))
    for r in relators:
        expression = regina.GroupExpression()
        for x in r['word']:
            expression.addTermLast(label[abs(x)], 1 if x > 0 else -1)
        presentation.addRelation(expression)
    presentation.simplify()
    result = presentation.recogniseGroup()
    return result


def corruptions(certificate):
    for key in certificate:
        value = deepcopy(certificate)
        del value[key]
        yield 'missing_' + key, value
    yield 'extra_key', dict(certificate, unexpected=0)
    for key, incorrect in [
        ('schema', 'wrong'), ('policy', 'wrong'), ('presentation_sha256', '0'*64),
        ('free_rank', -1), ('free_rank', float(certificate['free_rank'])),
        ('free_rank', True), ('free_generators', certificate['free_generators'] + [10**6]),
        ('trivial_relators', certificate['trivial_relators'] + [10**6]),
        ('initial_reduced_length', certificate['initial_reduced_length'] + 1),
        ('moves', [[10**9, 10**9]]), ('moves', [True]),
    ]:
        value = deepcopy(certificate)
        value[key] = incorrect
        yield 'invalid_' + key, value
    if certificate['moves']:
        for i in range(len(certificate['moves'])):
            value = deepcopy(certificate)
            value['moves'][i][1] = -value['moves'][i][1]
            yield 'negative_pivot_' + str(i), value
            value = deepcopy(certificate)
            value['moves'][i][1] = True
            yield 'boolean_pivot_' + str(i), value
        value = deepcopy(certificate)
        value['moves'] = value['moves'][:-1]
        yield 'truncated_trace', value
        value = deepcopy(certificate)
        value['moves'].append(value['moves'][-1][:])
        yield 'duplicated_pivot', value


def target_presentations(path):
    """Read either a compiled presentation or a saved source certificate packet.

    Supported packets contain a certificate directly, under ``certificate``,
    or under ``result.certificate``.  Reading its presentations here is not
    a substitute for independently authenticating its topological source.
    """
    value = json.loads(path.read_text())
    if type(value) is not dict:
        raise ValueError('target must be a JSON object')
    if value.get('schema') == 'source-disk-cut-presentation-v1':
        return value, {}
    if type(value.get('result')) is dict:
        value = value['result']
    if type(value.get('certificate')) is dict:
        value = value['certificate']
    presentation = value.get('presentation')
    if (type(presentation) is not dict
            or presentation.get('schema') != 'source-disk-cut-presentation-v1'):
        raise ValueError('target has no supported compiled group presentation')
    proofs = {record['component']: record['proof'] for record in value.get('groups', [])}
    return presentation, proofs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path, required=True,
                        help='Directory containing the integrated fastunknot package')
    parser.add_argument('--target', type=Path,
                        help='Optional compiled presentation or saved figure-eight packet JSON')
    parser.add_argument('--output', type=Path, required=True,
                        help='JSON report destination')
    args = parser.parse_args()
    if not __debug__:
        parser.error('run without -O: this audit requires Python assertions')
    fast = args.fast_root.resolve()
    source_files = [fast / 'fastunknot' / filename for filename in (
        'free_group_elimination.py', 'free_group_elimination_verify.py')]
    if any(not path.is_file() for path in source_files):
        parser.error('--fast-root must contain the freeness producer and checker')
    sys.path.insert(0, str(fast))
    from fastunknot.free_group_elimination import certify_free_group
    from fastunknot.free_group_elimination_verify import replay_free_group
    import regina

    rng = random.Random(20261012)
    summary = Counter()
    recognized = Counter()
    worst = {'accepted_length': 0, 'trial_visits': 0, 'certificate_bytes': 0}
    examples = []

    def case(generators, words, source, external=False, mutate=False):
        rows = [dict(id=i*7+3, word=list(w)) for i, w in enumerate(words)]
        result = certify_free_group(generators, rows)
        summary['cases'] += 1
        summary[source] += 1
        summary[result['status']] += 1
        if result['status'] != 'COMPLETE':
            return result
        cert = result['certificate']
        replayed = replay_free_group(generators, rows, cert)
        assert replayed is not None
        images, lengths = explicit_isomorphism(generators, rows, cert)
        assert lengths == result['accepted_lengths'] == replayed['accepted_lengths']
        assert max(lengths) <= result['stats']['initial_reduced_length']
        assert len(cert['moves']) <= min(len(generators), len(rows))
        summary['explicit_isomorphisms'] += 1
        worst['accepted_length'] = max(worst['accepted_length'], max(lengths))
        worst['trial_visits'] = max(worst['trial_visits'], result['stats']['trial_letter_visits'])
        worst['certificate_bytes'] = max(worst['certificate_bytes'], len(json.dumps(cert)))
        if external:
            if len(generators) <= 3:
                assert s3_homs(generators, rows) == 6**result['free_rank']
                summary['nonabelian_S3_checks'] += 1
            name = regina_recognize(generators, rows)
            expected = '0' if result['free_rank'] == 0 else 'Z' if result['free_rank'] == 1 else f'Free({result["free_rank"]})'
            assert name == expected, (source, generators, words, name, expected)
            recognized[name] += 1
            summary['regina_checks'] += 1
        if mutate:
            for name, damaged in corruptions(cert):
                assert replay_free_group(generators, rows, damaged) is None, name
                summary['rejected_certificate_mutations'] += 1
        if source == 'figureeight':
            examples.append(dict(rank=result['free_rank'], pivots=len(cert['moves']),
                                 lengths=lengths, images={str(g): list(w) for g,w in images.items()},
                                 stats=result['stats']))
        return result

    # Exhaustive two-generator one-relator presentations through length five.
    alphabet = (1, -1, 2, -2)
    for length in range(6):
        for word in product(alphabet, repeat=length):
            case([1, 2], [word], 'single_relator_exhaustive',
                 external=(rng.random() < 0.08), mutate=(rng.random() < 0.02))
    # Exhaustive pairs of relators through length three.
    short = [w for n in range(4) for w in product(alphabet, repeat=n)]
    for first, second in product(short, repeat=2):
        case([1, 2], [first, second], 'two_relators_exhaustive',
             external=(rng.random() < 0.04), mutate=(rng.random() < 0.01))
    # Sparse labels and mixed signs exercise dictionaries and inverse substitutions.
    for _ in range(1600):
        generators = rng.sample([1, 3, 7, 101, 1000003], rng.randrange(1, 4))
        alphabet = generators + [-g for g in generators]
        words = [tuple(rng.choice(alphabet) for _ in range(rng.randrange(0, 10)))
                 for _ in range(rng.randrange(0, 5))]
        case(generators, words, 'random_sparse', external=(rng.random() < 0.20),
             mutate=(rng.random() < 0.05))
    # Structural counterexamples: these are not free despite torsion-free H_1.
    for name, words in {
        'Z2': [(1, 2, -1, -2)],
        'trefoil': [(1, 1, -2, -2, -2)],
        'Klein_bottle': [(1, 2, -1, 2)],
        'torsion': [(1, 1)],
    }.items():
        result = case([1,2], words, 'known_nonfree')
        assert result['status'] == 'INCONCLUSIVE', name
    # Apply the free-group automorphism a->ab, b->a four times to the
    # standard trivial presentation.  Its relators have no singleton
    # occurrences.  This proves that the current policy is incomplete even
    # on trivial groups, while showing that failure remains inconclusive.
    fibonacci_words = [(1,), (2,)]
    for _ in range(4):
        fibonacci_words = [apply(w, {1: (1,2), 2: (1,)}) for w in fibonacci_words]
    for generators, expected in [([1,2], '0'), ([1,2,3], 'Z')]:
        result = case(generators, fibonacci_words, 'known_free_inconclusive')
        assert result['status'] == 'INCONCLUSIVE'
        rows = [dict(id=i, word=list(w)) for i,w in enumerate(fibonacci_words)]
        assert regina_recognize(generators, rows) == expected
        summary['regina_checks'] += 1
        summary['regina_certifies_inconclusive_case_is_free'] += 1
    # No-generator edge cases and trivial presentations.
    for generators, words in [([], []), ([], [()]), ([17], [()]),
                              ([17], [(17,-17)]), ([17], [(17,)])]:
        case(generators, words, 'edge_cases', external=True, mutate=True)
    if args.target is not None:
        compiled, saved_proofs = target_presentations(args.target)
        for component in compiled['components']:
            case(component['generators'], [r['word'] for r in component['relators']],
                 'figureeight', external=True, mutate=True)
            if component['id'] in saved_proofs:
                proof = saved_proofs[component['id']]
                assert replay_free_group(component['generators'], component['relators'], proof)
                explicit_isomorphism(component['generators'], component['relators'], proof)
                summary['saved_target_certificates_replayed'] += 1
    out = dict(summary=summary, regina_recognized=recognized, maxima=worst,
               figureeight=examples,
               explicit_incomplete_policy_example={
                   'generators': [1,2],
                   'relators': [list(w) for w in fibonacci_words],
                   'group': 'trivial',
                   'producer_status': 'INCONCLUSIVE',
                   'reason': 'Fourth iterate of a->ab,b->a applied to standard relators.'},
               source_sha256={path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in source_files},
               target_sha256=(hashlib.sha256(args.target.read_bytes()).hexdigest()
                              if args.target is not None else None),
               random_seed=20261012,
               python=sys.version,
               regina=regina.versionString(),
               scope='Exact presentation isomorphisms and independent algebra oracles; no geometric certification claim.',
               timing_claim='none: this is a correctness audit, not a benchmark')
    output = args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
