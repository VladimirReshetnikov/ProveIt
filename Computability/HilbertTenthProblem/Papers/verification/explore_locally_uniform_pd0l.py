"""Exact locally uniform resampling and the aligned finite-graph lemma."""
from itertools import product
from pathlib import Path
import json


ALPHABET = (1, 2)
BASE = 3


def words(maximum):
    return [word for length in range(maximum+1)
            for word in product(ALPHABET, repeat=length)]


def code(word):
    return sum(letter*BASE**i for i, letter in enumerate(word))


def prefixes(lengths):
    result = [0]
    for length in lengths:
        result.append(result[-1]+length)
    return result


def apply(images, word):
    p = len(images)
    return tuple(child for i, letter in enumerate(word)
                 for child in images[i % p][letter])


def valid_lengths(images, lengths):
    assert len(images) == len(lengths)
    assert all(len(images[r][a]) == length
               for r, length in enumerate(lengths) for a in ALPHABET)


def image_family(lengths, seed, slope):
    result = []
    for phase, length in enumerate(lengths):
        mapping = {}
        for letter in ALPHABET:
            pattern = (seed+phase+slope*(letter-1)) % 4
            mapping[letter] = tuple(1+((pattern if pattern < 2 else
                                       j+pattern-2) % 2) for j in range(length))
        result.append(mapping)
    valid_lengths(result, lengths)
    return result


def exact_resampling(images, lengths, word):
    p, K = len(lengths), sum(lengths)
    kappa = prefixes(lengths)
    source = target = wrong = 0
    E = {}
    for r, letter in product(range(p), ALPHABET):
        powers = [t for t in range((len(word)+p-1)//p)
                  if p*t+r < len(word) and word[p*t+r] == letter]
        before = sum(BASE**(p*t) for t in powers)
        after = sum(BASE**(K*t) for t in powers)
        E[r, letter] = (before, after)
        source += letter*BASE**r*before
        coefficient = code(images[r][letter])*BASE**kappa[r]
        target += coefficient*after
        wrong += coefficient*before
    actual = apply(images, word)
    assert source == code(word) and target == code(actual)
    assert len(actual) == K*(len(word)//p)+kappa[len(word) % p]
    cursor = 0
    phases = 0
    for j, letter in enumerate(word):
        t, r = divmod(j, p)
        assert cursor == K*t+kappa[r]
        for offset, child in enumerate(images[r][letter]):
            position = K*t+kappa[r]+offset
            assert actual[position] == child
            assert (cursor+offset) % p == position % p
            phases += 1
        cursor += lengths[r]
    return E, target, wrong, phases


def resampling_checks():
    cases = erased = partial = nonaligned = phases = 0
    vectors = [(2,), (0, 3), (1, 2), (1, 3), (2, 2),
               (3, 1), (0, 1, 5), (1, 2, 3), (2, 1, 1)]
    for lengths in vectors:
        for seed, slope in product(range(4), range(4)):
            images = image_family(lengths, seed, slope)
            for word in words(6):
                _, _, _, count = exact_resampling(images, lengths, word)
                cases += 1
                erased += bool(word) and 0 in lengths
                partial += len(word) % len(lengths) != 0
                nonaligned += sum(lengths) % len(lengths) != 0
                phases += count
    images = [{a: (a,) for a in ALPHABET}, {a: (a, a) for a in ALPHABET}]
    E, actual, wrong, _ = exact_resampling(images, (1, 2), (1, 2, 1, 2))
    assert E[0, 1] == E[1, 2] == (10, 28)
    assert (actual, wrong) == (700, 250)
    word = (1, 2, 1, 2)
    child_starts = [len(apply(images, word[:j])) for j in (0, 2)]
    assert child_starts == [0, 3]
    return dict(word_cases=cases, erased_phase_cases=erased,
                partial_phase_cycle_cases=partial, nonaligned_cases=nonaligned,
                checked_child_positions=phases,
                explicit_nonaligned=dict(period=2, lengths=[1, 2], input=[1, 2, 1, 2],
                    input_indicator=10, output_indicator=28, true_output=actual,
                    wrong_reused_indicator_output=wrong,
                    child_start_phases=[start % 2 for start in child_starts]))


def length_map(lengths, n):
    p, K = len(lengths), sum(lengths)
    return K*(n//p)+sum(lengths[:n % p])


def productive(lengths, initial_length):
    p, K = len(lengths), sum(lengths)
    if initial_length == 0 or K <= p:
        return False
    first = [initial_length+(r-initial_length) % p for r in range(p)]
    return all(length_map(lengths, n) > n for n in first)


def productivity_checks():
    cases = productive_cases = stabilized = erased = 0
    for p in (1, 2, 3):
        for lengths in product(range(4), repeat=p):
            for initial_length in range(13):
                if length_map(lengths, initial_length) < initial_length:
                    continue  # Not a possible prefix-prolongable seed length.
                yes = productive(lengths, initial_length)
                n = initial_length
                stopped = False
                for _ in range(100):
                    after = length_map(lengths, n)
                    assert after >= n
                    if after == n:
                        stopped = True
                        break
                    n = after
                assert yes != stopped
                cases += 1
                productive_cases += yes
                stabilized += stopped
                erased += 0 in lengths
    return dict(admissible_length_cases=cases, productive_cases=productive_cases,
                finite_stabilized_cases=stabilized, erased_phase_cases=erased,
                scalar_iteration_limit=100)


def block_image(images, block):
    p = len(images)
    output = apply(images, block)
    assert len(block) == p and len(output) % p == 0
    return tuple(output[i:i+p] for i in range(0, len(output), p))


def flatten(blocks):
    return tuple(a for block in blocks for a in block)


def aligned_checks():
    vectors = [(2,), (0, 4), (1, 3), (2, 2), (3, 1), (4, 0),
               (0, 1, 5), (1, 2, 3), (2, 2, 2), (5, 1, 0)]
    systems = cases = nonmultiple = longer_seed = erased = mixed = finite = 0
    commutations = marker_comparisons = 0
    records = []
    for lengths in vectors:
        p, K = len(lengths), sum(lengths)
        assert K % p == 0 and K//p == 2
        for pattern, slope in product(range(4), range(4)):
            images = image_family(lengths, pattern, slope)
            systems += 1
            for seed in words(p+2):
                first = apply(images, seed)
                if first[:len(seed)] != seed:
                    continue
                if not productive(lengths, len(seed)):
                    word = seed
                    for _ in range(100):
                        nxt = apply(images, word)
                        if nxt == word:
                            break
                        word = nxt
                    else:
                        raise AssertionError('Finite limit failed to stabilize')
                    finite += 1
                    continue
                word = seed
                while len(word) < p:
                    word = apply(images, word)
                initial = word[:p]
                assert flatten(block_image(images, initial))[:p] == initial
                reached, pending = {initial}, [initial]
                while pending:
                    block = pending.pop()
                    for child in block_image(images, block):
                        if child not in reached:
                            reached.add(child)
                            pending.append(child)
                assert len(reached) <= len(ALPHABET)**p
                blocks = (initial,)
                for _ in range(len(ALPHABET)**p):
                    next_blocks = tuple(child for block in blocks
                                        for child in block_image(images, block))
                    assert flatten(next_blocks) == apply(images, flatten(blocks))
                    assert next_blocks[:len(blocks)] == blocks
                    blocks = next_blocks
                    commutations += 1
                expanded = flatten(blocks)
                assert set(blocks) == reached
                assert expanded[:len(seed)] == seed
                reachable_letters = {a for block in reached for a in block}
                assert reachable_letters == set(expanded)
                for marker in ALPHABET:
                    assert (marker in reachable_letters) == (marker in expanded)
                    marker_comparisons += 1
                cases += 1
                nonmultiple += len(seed) % p != 0
                longer_seed += len(seed) > p
                erased += 0 in lengths
                mixed += len(set(lengths)) > 1
                if len(records) < 12 and len(seed) % p and 0 in lengths:
                    records.append(dict(lengths=lengths, seed=seed,
                                        initial_block=initial, reachable_blocks=len(reached)))
    assert min(cases, nonmultiple, longer_seed, erased, mixed, finite, len(records)) > 0
    return dict(systems=systems, productive_seed_cases=cases,
                nonmultiple_seed_cases=nonmultiple, seeds_longer_than_block=longer_seed,
                productive_erasing_cases=erased, nonconstant_length_cases=mixed,
                finite_seed_limits=finite, block_commutations=commutations,
                marker_membership_comparisons=marker_comparisons, erasing_examples=records,
                scope='Finite aligned examples only; the graph theorem is proved separately.')


def verify():
    return dict(status='PASS_LOCALLY_UNIFORM_PD0L_RESAMPLING',
                resampling=resampling_checks(), productivity=productivity_checks(),
                aligned=aligned_checks(), proof='../1980/EXPLORATION_LOCALLY_UNIFORM_PD0L.md',
                review='Author and two independent complete scoped proof/source reviews and fresh receipt checks PASS.',
                scope='Exact simultaneous resampling and decidable aligned p|K subclass only; '
                      'general locally uniform marker occurrence and universal certificate cost remain open here.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    for name in ('resampling', 'productivity', 'aligned'):
        print(name, {k: v for k, v in result[name].items() if k != 'erasing_examples'})
