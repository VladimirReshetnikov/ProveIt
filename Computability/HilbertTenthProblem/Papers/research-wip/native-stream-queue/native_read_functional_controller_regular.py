#!/usr/bin/env python3
"""Finite independent checks for controlled read-functional FIFO regularity.

The adjacent note proves regularity for arbitrary finite alphabets/controllers.
This checker compares its finite-monoid decision procedure with exhaustive
physical queue reachability, without a time cutoff. No Pell witness or new
universal operation bound is claimed.
"""
import argparse
from collections import deque
from itertools import product
import json
from pathlib import Path


def identity(n):
    return tuple(1 << i for i in range(n))


def compose(left, right):
    """Boolean relation composition, in temporal left-to-right order."""
    answer = []
    for row in left:
        value = 0
        while row:
            bit = row & -row
            value |= right[bit.bit_length() - 1]
            row -= bit
        answer.append(value)
    return tuple(answer)


def function_powers(rewrite):
    current = tuple(range(len(rewrite)))
    sequence, seen = [], {}
    while current not in seen:
        seen[current] = len(sequence)
        sequence.append(current)
        current = tuple(rewrite[x] for x in current)
    start = seen[current]
    successor = tuple(i + 1 if i + 1 < len(sequence) else start
                      for i in range(len(sequence)))
    return tuple(sequence), successor, start, len(sequence) - start


def make_controller(rewrite, rows, first=None, modulus=1):
    """Two ordinary states, OR flags, optional prescribed first edge/clock.

    rows[a] is a four-bit relation, bit(2*source+target). Every physical
    append is rewrite[a]. Flags require a nonzero read and nonzero append.
    A dedicated entry state imposes first=(symbol, target), if supplied.
    """
    ordinary = 2 * 4 * modulus
    size = ordinary + int(first is not None)

    def index(state, mask, phase):
        return (state * 4 + mask) * modulus + phase

    matrices = []
    for symbol, relation in enumerate(rows):
        table = [0] * size
        event = int(symbol != 0) | (2 * int(rewrite[symbol] != 0))
        for state, mask, phase in product(range(2), range(4), range(modulus)):
            targets = 0
            for target in range(2):
                if relation & (1 << (2 * state + target)):
                    targets |= 1 << index(target, mask | event,
                                          (phase + 1) % modulus)
            table[index(state, mask, phase)] = targets
        if first is not None and symbol == first[0]:
            target = first[1]
            if relation & (1 << target):  # the prescribed edge starts in state 0
                table[ordinary] = 1 << index(target, event, 1 % modulus)
        matrices.append(tuple(table))
    initial = ordinary if first is not None else index(0, 0, 0)
    final = 1 << index(1, 3, 0)
    return tuple(matrices), initial, final


def physical_reachability(word, rewrite, matrices, initial, final):
    """Exhaust the finite physical queue/controller graph, not a time prefix."""
    start = (word, initial)
    pending, seen = deque([start]), {start}
    while pending:
        queue, state = pending.popleft()
        if not any(queue) and final & (1 << state):
            return True, len(seen)
        targets = matrices[queue[0]][state]
        next_queue = queue[1:] + (rewrite[queue[0]],)
        while targets:
            bit = targets & -targets
            target = bit.bit_length() - 1
            node = (next_queue, target)
            if node not in seen:
                seen.add(node)
                pending.append(node)
            targets -= bit
    return False, len(seen)


def monoid_reachability(word, rewrite, matrices, initial, final):
    """Decide all durations from full-sweep relation and finite f-power phase."""
    powers, successor, _, _ = function_powers(rewrite)
    ident = identity(len(matrices[0]))
    prefixes = []
    for mapping in powers:
        current, row = ident, [ident]
        for symbol in word:
            current = compose(current, matrices[mapping[symbol]])
            row.append(current)
        prefixes.append(tuple(row))
    full = tuple(row[-1] for row in prefixes)
    previous, sweep, phase = set(), ident, 0
    while (sweep, phase) not in previous:
        previous.add((sweep, phase))
        current_map, next_map = powers[phase], powers[successor[phase]]
        # Canonical duration h*m+p has 0<=p<m, so the suffix is nonempty.
        for cut in range(len(word)):
            if (any(next_map[a] != 0 for a in word[:cut])
                    or any(current_map[a] != 0 for a in word[cut:])):
                continue
            after_partial = compose(sweep, prefixes[phase][cut])
            if after_partial[initial] & final:
                return True, len(previous)
        sweep = compose(sweep, full[phase])
        phase = successor[phase]
    return False, len(previous)


def compare_system(rewrite, rows, words, first=None, modulus=1):
    matrices, initial, final = make_controller(rewrite, rows, first, modulus)
    comparisons = accepted = max_physical = max_sweep = 0
    for word in words:
        actual, physical_states = physical_reachability(
            word, rewrite, matrices, initial, final)
        predicted, sweep_states = monoid_reachability(
            word, rewrite, matrices, initial, final)
        assert actual == predicted, (rewrite, rows, word, first, modulus,
                                     actual, predicted)
        comparisons += 1
        accepted += actual
        max_physical = max(max_physical, physical_states)
        max_sweep = max(max_sweep, sweep_states)
    return comparisons, accepted, max_physical, max_sweep


def check():
    results = []
    function_checks = 0
    for size in (2, 3):
        for rewrite in product(range(size), repeat=size):
            powers, successor, _, _ = function_powers(rewrite)
            actual = tuple(range(size))
            phase = 0
            for _ in range(100):
                assert powers[phase] == actual
                actual = tuple(rewrite[a] for a in actual)
                phase = successor[phase]
                function_checks += 1

    # Exhaust every Boolean relation on two controller states for each of
    # two read symbols, with every read-functional binary rewrite map.
    binary_words = [word for length in range(1, 5)
                    for word in product(range(2), repeat=length)]
    for rewrite in product(range(2), repeat=2):
        for rows in product(range(16), repeat=2):
            results.append(compare_system(rewrite, rows, binary_words))
    binary_systems = len(results)

    # Ternary fixture family includes blocked, identity, toggle, total,
    # asymmetric nondeterministic and partial controller relations.
    fixtures = ((0, 15, 9), (9, 6, 15), (3, 12, 15), (5, 10, 6),
                (15, 15, 15), (9, 9, 9), (6, 6, 6), (1, 8, 7))
    ternary_words = [word for length in range(1, 4)
                     for word in product(range(3), repeat=length)]
    ternary_systems = 0
    aligned_first_systems = 0
    for rewrite in product(range(3), repeat=3):
        for rows in fixtures:
            results.append(compare_system(rewrite, rows, ternary_words))
            ternary_systems += 1
            # Paid even width/time and a prescribed first edge are all
            # finite restrictions, independently exercised here.
            for first in ((0, 0), (1, 1), (2, 0)):
                even_words = [word for word in ternary_words if len(word) % 2 == 0]
                results.append(compare_system(rewrite, rows, even_words,
                                              first=first, modulus=2))
                aligned_first_systems += 1

    # Physical rewrites can leave zero, so zero absorption is never assumed.
    # f toggles 0/1; a controller toggle accepts from initial 1 after one
    # step. This separate fixture omits positive-append flags intentionally.
    matrices = ((2, 1), (2, 1))
    actual = physical_reachability((1,), (1, 0), matrices, 0, 2)[0]
    predicted = monoid_reachability((1,), (1, 0), matrices, 0, 2)[0]
    assert actual is predicted is True

    return {
        'status': 'PASS_READ_FUNCTIONAL_CONTROLLED_FIFO',
        'binary_exhaustive_systems': binary_systems,
        'ternary_fixture_systems': ternary_systems,
        'even_width_time_first_edge_systems': aligned_first_systems,
        'complete_reachability_comparisons': sum(r[0] for r in results) + 1,
        'accepting_comparisons': sum(r[1] for r in results) + 1,
        'maximum_physical_states_seen': max(r[2] for r in results),
        'maximum_sweep_summary_states_seen': max(r[3] for r in results),
        'function_power_checks': function_checks,
        'controller_flags': ['nonzero read', 'nonzero append'],
        'duration_cutoff': None,
        'zero_absorbing_assumption': False,
        'scope': 'Finite independent full-graph comparisons; arbitrary-size '
                 'regularity follows from the adjacent mathematical proof.',
        'new_arithmetic_schedule': False,
        'established_complete_bound': 75,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = check()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(receipt.read_text()) == result
    print(json.dumps(result, indent=2))
