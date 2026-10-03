"""Exact finite-window structure of the fixed Boolean-labelled carry graph."""
import argparse
from itertools import product
import json
from pathlib import Path


def bound_and_memory(coefficients, h, cs):
    bound = max(abs(cs), (abs(h) + sum(map(abs, coefficients)) + 1) // 2)
    memory = 1
    while 3 ** memory <= 2 * bound:
        memory += 1
    return bound, memory


def direct_paths(word, bound):
    paths = []
    for start in range(-bound, bound + 1):
        carry = start
        for increment in word:
            numerator = carry + increment
            if numerator % 3:
                break
            carry = numerator // 3
            assert -bound <= carry <= bound
        else:
            paths.append((start, carry))
    return tuple(paths)


def residue_path(word, bound):
    modulus = 3 ** len(word)
    assert modulus > 2 * bound
    weighted = sum(increment * 3 ** j for j, increment in enumerate(word))
    start = -bound + ((-weighted + bound) % modulus)
    if start > bound:
        return None
    end = (start + weighted) // modulus
    assert -bound <= end <= bound
    return start, end


def windows_path(word, memory, prefix_table, window_table):
    assert len(word) >= memory
    prefix = prefix_table.get(word[:memory])
    suffix = prefix_table.get(word[-memory:])
    if prefix is None or suffix is None:
        return None
    if any(word[j:j + memory + 1] not in window_table
           for j in range(len(word) - memory)):
        return None
    return prefix[0], suffix[1]


def audit_model(bound, increments):
    memory = 1
    while 3 ** memory <= 2 * bound:
        memory += 1
    prefix_table = {}
    for word in product(increments, repeat=memory):
        path = residue_path(word, bound)
        if path is not None:
            prefix_table[word] = path
    window_table = set()
    for word in product(increments, repeat=memory + 1):
        if residue_path(word, bound) is not None:
            window_table.add(word)

    short_words = long_words = feasible_long = injectivity = 0
    for length in range(memory + 4):
        for word in product(increments, repeat=length):
            paths = direct_paths(word, bound)
            assert len({end for _, end in paths}) == len(paths)
            injectivity += 1
            if length < memory:
                short_words += 1
                # The endpoint equation implies each intermediate divisibility.
                weighted = sum(value * 3 ** j for j, value in enumerate(word))
                recovered = tuple((start, (start + weighted) // 3 ** length)
                                  for start in range(-bound, bound + 1)
                                  if (start + weighted) % 3 ** length == 0)
                assert recovered == paths
                continue
            assert len(paths) <= 1
            recovered = residue_path(word, bound)
            local = windows_path(word, memory, prefix_table, window_table)
            expected = paths[0] if paths else None
            assert recovered == local == expected
            feasible_long += bool(paths)
            long_words += 1

    powers = 0
    for length in range(1, memory + 2):
        for block in product(increments, repeat=length):
            action = dict(direct_paths(block, bound))
            for start in range(-bound, bound + 1):
                carry = start
                hits = {start: [0]}
                for exponent in range(1, 7):
                    if carry not in action:
                        break
                    carry = action[carry]
                    hits.setdefault(carry, []).append(exponent)
                for exponents in hits.values():
                    if len(exponents) >= 2:
                        assert exponents == list(range(7))
                    powers += 1
    return dict(bound=bound, memory=memory, increments=list(increments),
                short_words=short_words, long_words=long_words,
                feasible_long_words=feasible_long, injectivity_checks=injectivity,
                repeated_block_endpoint_sets=powers)


def verify():
    cases = collisions = 0
    signatures = set()
    for coefficients in product(range(-1, 2), repeat=4):
        for h in range(-1, 2):
            labels = list(product((0, 1), repeat=4))
            increments = tuple(sorted({h + sum(c * bit for c, bit in zip(coefficients, label))
                                       for label in labels}))
            # A carry edge depends only on this weighted label. The FIFO may
            # still distinguish labels in the same class.
            for left, right in product(labels, repeat=2):
                gl = h + sum(c * bit for c, bit in zip(coefficients, left))
                gr = h + sum(c * bit for c, bit in zip(coefficients, right))
                if gl == gr:
                    for state in range(-3, 4):
                        assert (state + gl) % 3 == (state + gr) % 3
                        assert (state + gl) // 3 == (state + gr) // 3
                    collisions += 1
            for cs in range(-2, 3):
                bound, memory = bound_and_memory(coefficients, h, cs)
                assert 3 ** memory > 2 * bound
                assert all(abs(value) <= 2 * bound for value in increments)
                signatures.add((bound, increments))
                cases += 1
    models = [audit_model(bound, increments) for bound, increments in sorted(signatures)]
    totals = {key: sum(row[key] for row in models) for key in (
        'short_words', 'long_words', 'feasible_long_words', 'injectivity_checks',
        'repeated_block_endpoint_sets')}
    return dict(status='PASS_EXACT_CARRY_FINITE_WINDOW_CHARACTERIZATION',
                coefficient_offset_start_cases=cases,
                distinct_bounded_weighted_alphabet_models=len(models),
                equal_weight_label_pairs=collisions,
                maximum_bound=max(row['bound'] for row in models),
                maximum_memory=max(row['memory'] for row in models),
                totals=totals, models=models,
                scope='Exact carry-language windows and compiler criteria; no FIFO universality or decidability claim',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps({key: value for key, value in result.items() if key != 'models'}, indent=2))
