#!/usr/bin/env python3
"""Finite box-state folds with an existential valid spare suffix.

This diagnostic deliberately changes rows excluded by the earlier affine
searches. Every sample-stage step is literal, with no unchanged-box oracle.
A later conditional instruction screen uses proposed renamed macro outputs.
Passing samples is not an unbounded box proof, runtime proof or blank-start claim.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import tempfile
import time

import candidate252_independent_audit as baseline
import breakthrough_register_permutation as affine


def paint(values):
    bits = []
    for value in values:
        bits += [0] + [1] * (value + 1)
    return bits


def samples():
    """Every selected index, four operations, several files and one left context."""
    vectors = [[0] * 9, [1] * 9, [2] * 9,
               [i % 3 for i in range(9)], [(8 - i) % 3 for i in range(9)]]
    for op in ('mark', 'inc', 'dec0', 'decp'):
        for r in range(9):
            for vector in vectors:
                for spare in ([], [0], [2, 0, 1]):
                    values = vector.copy()
                    if op == 'dec0':
                        values[r] = 0
                    if op == 'decp':
                        values[r] = max(1, values[r])
                    mark = sum(v + 2 for v in values[:r]) + 1
                    raw = paint(values + spare)
                    if op != 'mark':
                        raw[mark] = 0
                    wanted = values.copy()
                    if op == 'inc':
                        wanted[r] += 1
                    if op == 'decp':
                        wanted[r] -= 1
                    prefix = paint(wanted)
                    if op == 'mark':
                        prefix[mark] = 0
                    start = baseline.SKIP[r] if op == 'mark' else 73 if op == 'inc' else 43
                    stop = (2 if r == 0 else 6) if op == 'mark' else 48 if op == 'inc' else 3 if op == 'dec0' else (63 if r == 0 else 48)
                    # The left context includes the header and two separated PC bits.
                    left = {-1, -4, -7}
                    ones = left | {i for i, b in enumerate(raw) if b}
                    yield dict(op=op, register=r, values=values, spares=spare,
                               start=start, stop=stop, ones=ones, left=left, prefix=prefix)


def run(table, case, fuel, dead=None, target=None):
    relocate = lambda q: target if q == dead else q
    state, head, ones = relocate(case['start']), 0, case['ones'].copy()
    used = set()
    for tick in range(fuel):
        if state == 254:
            return False, 'halt', used, tick
        row = state, int(head in ones)
        used.add(row)
        write, direction, state = table[row]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
        if head >= 0:
            continue
        # This family keeps the box boundary fixed: its first exit must be
        # the corresponding relocated return state at the header.
        if head != -1 or state != relocate(case['stop']):
            return False, 'first_exit_state', used, tick + 1
        if {i for i in ones if i < 0} != case['left']:
            return False, 'left_context', used, tick + 1
        prefix = case['prefix']
        if any(int(i in ones) != b for i, b in enumerate(prefix)):
            return False, 'primary_registers', used, tick + 1
        # Accept any finite sequence of well-formed spare blocks, including
        # none. Check every remaining one; exterior blank is implicit.
        cursor, end = len(prefix), max(ones)
        while cursor <= end:
            if cursor in ones or cursor + 1 not in ones:
                return False, 'spare_shape', used, tick + 1
            cursor += 1
            while cursor in ones:
                cursor += 1
        return True, None, used, tick + 1
    return False, 'fuel', used, fuel


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=120)
    parser.add_argument('--fuel', type=int, default=1000)
    args = parser.parse_args()
    if not __debug__ or args.seconds <= 0 or args.fuel <= 0:
        parser.error('Assertions and positive bounds are required')
    source = baseline.ROOT / 'Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm'
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == baseline.EXPECTED_SHA
    table = baseline.read_table(raw)
    cases = list(samples())
    usage = []
    for i, case in enumerate(cases):
        ok, reason, used, _ = run(table, case, args.fuel)
        assert ok, ('baseline', i, reason)
        usage.append(used)
    states = sorted({q for q, _ in table})
    protected_targets = {table[k][2] for k in baseline.BOX_PAIRS}
    deleted = sorted((baseline.BOX_STATES | protected_targets) - {64, 96})
    recipes = [(q, r) for q in deleted for r in states if r != q]
    result = dict(status='running', scope='Finite literal box samples with arbitrary valid spares; no unbounded, runtime, blank-start or consistency result.',
                  attribution='Mira-Cult/Jeff/Wade original254, mira-emmy public253, ProveIt permutation252.',
                  table_sha256=baseline.EXPECTED_SHA,
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  audit_helper_sha256=hashlib.sha256(Path(baseline.__file__).read_bytes()).hexdigest(),
                  baseline_samples=len(cases), baseline_status='PASS', fuel=args.fuel,
                  seconds_limit=args.seconds, planned=len(recipes), tested=0,
                  failures=[], survivors=[], candidate_samples=0)
    began = time.monotonic()
    reasons = Counter()
    for dead, target in recipes:
        if time.monotonic() - began >= args.seconds:
            break
        changed = {k: (w, d, target if t == dead else t)
                   for k, (w, d, t) in table.items() if k[0] != dead}
        assert len(changed) == 502
        # Prioritize samples that previously touched the deleted state or an
        # incoming row. All samples remain mandatory for every survivor.
        affected = {k for k, (_, _, t) in table.items() if k[0] == dead or t == dead}
        order = sorted(range(len(cases)), key=lambda i: not bool(usage[i] & affected))
        failure = None
        for i in order:
            ok, reason, _, ticks = run(changed, cases[i], args.fuel, dead, target)
            result['candidate_samples'] += 1
            if not ok:
                failure = [dead, target, i, reason, ticks]
                break
        result['tested'] += 1
        if failure is None:
            result['survivors'].append([dead, target])
        else:
            reasons[failure[3]] += 1
            result['failures'].append(failure)
    result.update(status='completed' if result['tested'] == len(recipes) else 'time_bound_partial',
                  elapsed_seconds=time.monotonic() - began, failure_reasons=dict(reasons),
                  remaining=len(recipes)-result['tested'])
    # These are conditional screens: the renamed oracle output is a proposed
    # macro contract supported only by the preceding finite literal samples.
    # No passed sample is promoted to an unbounded box theorem.
    scratch = Path(tempfile.mkdtemp(prefix='zfc-spare-fold-affine-'))
    inputs = affine.prepare(baseline.ROOT, scratch)
    original_oracle = affine.strict.oracle
    ordinary = {(str(q), b): (w, d, str(t)) for (q, b), (w, d, t) in table.items()}
    assert affine.certify(ordinary, baseline.PERM)['passed']
    result['conditional_affine'] = []
    result['conditional_scope'] = 'Proposed relocated box outputs; all changed box contracts still require unbounded proofs. Fuel1000. No blank runs.'
    result['affine_inputs'] = inputs
    result['affine_helper_sha256'] = hashlib.sha256(Path(affine.__file__).read_bytes()).hexdigest()
    for dead, target in result['survivors']:
        # Only return-state folds survived the literal screen, besides 7/9,
        # which are not entered by any box sample. No oracle input is deleted.
        assert dead in (3, 6, 7, 9, 48), dead
        def relocated(q, branch, state):
            answer = original_oracle(q, branch, state)
            if answer is None:
                return None
            exit_state, effect = answer
            return (str(target) if exit_state == str(dead) else exit_state), effect
        affine.strict.oracle = relocated
        changed = {k: (w, d, str(target) if t == str(dead) else t)
                   for k, (w, d, t) in ordinary.items() if k[0] != str(dead)}
        check = affine.certify(changed, baseline.PERM)
        result['conditional_affine'].append(dict(deleted=dead, target=target, **check))
    affine.strict.oracle = original_oracle
    result['conditional_runtime_survivors'] = [r for r in result['conditional_affine'] if r['passed']]
    result['total_elapsed_seconds'] = time.monotonic() - began
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'planned', 'tested', 'baseline_samples',
                      'candidate_samples', 'failure_reasons', 'remaining', 'total_elapsed_seconds')}, indent=2))
    print('Literal sample survivors:', len(result['survivors']),
          'conditional runtime survivors:', len(result['conditional_runtime_survivors']))


if __name__ == '__main__':
    main()
