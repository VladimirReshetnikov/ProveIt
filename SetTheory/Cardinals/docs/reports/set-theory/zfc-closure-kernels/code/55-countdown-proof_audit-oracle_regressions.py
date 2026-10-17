#!/usr/bin/env python3
"""Independent regressions of composed boxes and exhaustive guard splitting.

Three deliberately separate scopes are recorded:
(1) algebraic oracle contracts and rejection controls;
(2) the real interval scheduler with a supplied finite box-operation body,
    compared against an independent concrete natural-register evaluator;
(3) literal runs of the frozen binary table from explicitly prepared box
    inputs, including nonzero spares and whole-tape comparisons.

The finite body in (2) is a scheduler harness, not a Turing-machine execution.
The prepared excursions in (3) reset control/head at contract boundaries;
they are individual box checks, not a new complete interpreter certificate.
None of these finite tests proves an unbounded altered-machine theorem.
"""
from collections import Counter
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'binary_experiments'))
sys.path.insert(0, str(ROOT / 'root_experiments'))
import common as c
import multieffect as me
import split_guard_folds as splitting

spec = importlib.util.spec_from_file_location(
    'independent_original_strict', ROOT / 'binary_experiments/strict_affine.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
SKIP = {index: state for state, index in old.SKIP.items()}


def all_bounds():
    return tuple((0, None) for _ in range(9))


def algebra_checks():
    checks = 0
    for r in range(9):
        splitting.BOUNDS = all_bounds()
        plain = ('plain', None)
        _, selected = splitting.oracle(SKIP[r], None, plain)
        _, increased = splitting.oracle('73', None, selected)
        assert old.oracle(SKIP[r], None, increased) is None
        _, reselected = splitting.oracle(SKIP[r], None, increased)
        spares_before = me.STATS['appended_zero_spares']
        exit_state, canceled = splitting.oracle('43', None, reselected)
        assert exit_state == ('63' if r == 0 else '48')
        assert canceled == plain
        assert me.STATS['appended_zero_spares'] == spares_before + 1
        checks += 1

        initial = list(all_bounds())
        initial[r] = (0, 0)
        splitting.BOUNDS = tuple(initial)
        _, selected = splitting.oracle(SKIP[r], None, plain)
        assert splitting.oracle('43', None, selected) == ('3', plain)
        _, selected_again = splitting.oracle(SKIP[r], None, plain)
        assert splitting.oracle('43', None, selected_again) == ('3', plain)
        checks += 1

    splitting.BOUNDS = all_bounds()
    try:
        splitting.oracle('43', None, ('mark', 1, None))
    except splitting.NeedSplit as request:
        assert (request.r, request.pivot) == (1, 0)
    else:
        raise AssertionError('unknown current-value decrement was guessed')
    checks += 1
    bad = ('plain', ('dec', 1))
    try:
        splitting.oracle(SKIP[1], None, bad)
    except AssertionError:
        pass
    else:
        raise AssertionError('negative possible register value was accepted')
    checks += 1
    return {'status': 'PASS', 'checks': checks,
            'new_boundary_demonstrated': 'increment/remark/decrement cancels primary effect and appends one zero spare',
            'rejection_controls': ['unknown guard requests a split', 'possible negative primary value rejected']}


def concrete(sequence, initial):
    result = list(initial)
    appended = 0
    for op, r in sequence:
        if op == 'inc':
            result[r] += 1
        elif result[r]:
            result[r] -= 1
            appended += 1
    return tuple(result), appended


def belongs(values, intervals):
    return all(value >= lo and (hi is None or value <= hi)
               for value, (lo, hi) in zip(values, intervals))


def scheduler_checks():
    original_run = c.strict.run
    original_length = len(c.CASES)
    command_choices = [('inc', 0), ('dec', 0), ('inc', 1), ('dec', 1)]
    contracts = concrete_checks = passed_leaves = 0
    active_sequence, leaf_records, poison_positive = (), [], False

    def supplied_body(table, pc, branch, target, halt=False, fuel=1000):
        state, appended = ('plain', None), 0
        for op, r in active_sequence:
            _, state = splitting.oracle(SKIP[r], branch, state)
            following, state = splitting.oracle('73' if op == 'inc' else '43', branch, state)
            if op == 'dec' and following != '3':
                appended += 1
        if poison_positive and splitting.BOUNDS[0][0] > 0:
            raise AssertionError('adversarial positive branch failure')
        leaf_records.append((splitting.BOUNDS, me.vector(state[1]), appended))
        # This is a supplied finite-body scheduler harness, not literal TM time.
        return Counter({'supplied_finite_body': len(active_sequence)}), 1

    try:
        c.strict.run = supplied_body
        for branch in (None, (0, True), (0, False)):
            c.CASES.append(('test', 'TEST', None, None, branch, None))
            case_index = len(c.CASES) - 1
            for length in range(1, 5):
                for sequence in product(command_choices, repeat=length):
                    active_sequence, leaf_records = sequence, []
                    ok, reason, splits, leaves = splitting.check({}, case_index)
                    assert ok, (sequence, branch, reason)
                    assert leaves == len(leaf_records) == splits + 1
                    contracts += 1
                    passed_leaves += leaves
                    for a, b in product(range(6), repeat=2):
                        initial = (a, b) + (0,) * 7
                        if branch is not None and ((a == 0) != branch[1]):
                            continue
                        covering = [leaf for leaf in leaf_records if belongs(initial, leaf[0])]
                        assert len(covering) == 1, (sequence, branch, initial, covering)
                        _, offset, append_count = covering[0]
                        output = tuple(x + d for x, d in zip(initial, offset))
                        assert (output, append_count) == concrete(sequence, initial)
                        concrete_checks += 1
                    # Include representatives arbitrarily far into unbounded tails.
                    for intervals, offset, append_count in leaf_records:
                        initial = tuple(lo + 10_000 if hi is None else lo
                                        for lo, hi in intervals)
                        output = tuple(x + d for x, d in zip(initial, offset))
                        assert (output, append_count) == concrete(sequence, initial)
                        concrete_checks += 1

        c.CASES.append(('adversarial', 'TEST', None, None, None, None))
        case_index = len(c.CASES) - 1
        active_sequence = (('dec', 0),)
        poison_positive = True
        leaf_records = []
        ok, reason, splits, leaves = splitting.check({}, case_index)
        assert not ok and reason == 'adversarial positive branch failure'
        assert splits == 1 and leaves == 1
        poison_positive = False
        leaf_records = []
        ok, reason, splits, leaves = splitting.check({}, case_index, split_budget=0)
        assert not ok and reason == 'split_budget' and leaves == 0
    finally:
        c.strict.run = original_run
        del c.CASES[original_length:]
    return {'status': 'PASS', 'finite_sequence_contracts': contracts,
            'independent_concrete_comparisons': concrete_checks,
            'completed_interval_leaves': passed_leaves,
            'coverage': 'every sampled source-admissible vector lies in exactly one completed leaf',
            'adversarial_controls': ['one passing zero branch cannot hide a failing positive branch',
                                     'split-budget exhaustion is rejection'],
            'scope': 'real interval scheduler with a supplied finite box-operation body; not a binary runtime test'}


def file_ones(values):
    output, position = set(), 0
    for value in values:
        output.update(range(position + 1, position + value + 2))
        position += value + 2
    return output


LEFT = {-3, -1}


def run_literal(tape, state, steps):
    tape = set(tape)
    head = 0
    for _ in range(steps):
        bit = int(head in tape)
        write, direction, state = c.T[state, bit]
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += 1 if direction == 'R' else -1
        assert state != '254'
    return tape, state, head


def prepared_box_checks():
    excursions = literal_steps = spare_negative_controls = 0
    for r, value, spares in product(range(9), (0, 1, 3), ((), (0,), (2, 0, 1))):
        primary = [i % 3 for i in range(9)]
        primary[r] = value
        all_values = primary + list(spares)
        initial = LEFT | file_ones(all_values)
        prefix_width = sum(x + 2 for x in primary[:r])
        file_width = sum(x + 2 for x in all_values)
        marked = initial - {prefix_width + 1}

        time = 2 * prefix_width + 3
        assert run_literal(initial, SKIP[r], time) == (marked, '2' if r == 0 else '6', -1)
        excursions += 1
        literal_steps += time

        incremented = primary[:]
        incremented[r] += 1
        time = 2 * file_width + 3
        assert run_literal(marked, '73', time) == (LEFT | file_ones(incremented + list(spares)), '48', -1)
        excursions += 1
        literal_steps += time

        if value == 0:
            time = 2 * prefix_width + 5
            expected, exit_state = initial, '3'
        else:
            decremented = primary[:]
            decremented[r] -= 1
            time = 2 * file_width + 3
            expected = LEFT | file_ones(decremented + list(spares) + [0])
            wrong_without_spare = LEFT | file_ones(decremented + list(spares))
            assert expected != wrong_without_spare
            spare_negative_controls += 1
            exit_state = '63' if r == 0 else '48'
        assert run_literal(marked, '43', time) == (expected, exit_state, -1)
        excursions += 1
        literal_steps += time

        # Complete physical net-effect cancellation at prepared box boundaries.
        plus_tape = LEFT | file_ones(incremented + list(spares))
        plus_marked = plus_tape - {prefix_width + 1}
        time = 2 * prefix_width + 3
        assert run_literal(plus_tape, SKIP[r], time) == (plus_marked, '2' if r == 0 else '6', -1)
        excursions += 1
        literal_steps += time
        time = 2 * (file_width + 1) + 3
        canceled_tape, exit_state, head = run_literal(plus_marked, '43', time)
        assert canceled_tape == LEFT | file_ones(primary + list(spares) + [0])
        assert canceled_tape != initial
        assert (exit_state, head) == ('63' if r == 0 else '48', -1)
        excursions += 1
        literal_steps += time
    return {'status': 'PASS', 'prepared_excursions': excursions,
            'literal_binary_transitions': literal_steps,
            'omitted_zero_spare_negative_controls': spare_negative_controls,
            'primary_indices': 9, 'selected_values': [0, 1, 3],
            'spare_examples': [[], [0], [2, 0, 1]],
            'comparison': 'exact state, integer head and entire one-cell set with zero exterior',
            'scope': 'individual prepared box contracts; control/head reset between contract inputs'}


if __name__ == '__main__':
    started = time.monotonic()
    table_path = ROOT / 'upstream/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm'
    assert sha256(table_path.read_bytes()).hexdigest() == '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
    result = {'algebra': algebra_checks(), 'interval_scheduler': scheduler_checks(),
              'prepared_literal_boxes': prepared_box_checks(),
              'seconds': time.monotonic() - started,
              'source_sha256': {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
                                for path in (table_path, Path(me.__file__), Path(splitting.__file__),
                                             Path(c.__file__), ROOT / 'binary_experiments/strict_affine.py',
                                             Path(__file__))},
              'scope': 'regression evidence only; unbounded soundness is the separate mathematical composition proof'}
    target = ROOT / 'proof_audit/oracle_regression_results.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
