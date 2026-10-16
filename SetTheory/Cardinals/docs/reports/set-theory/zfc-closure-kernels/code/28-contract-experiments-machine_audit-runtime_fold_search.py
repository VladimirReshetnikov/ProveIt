#!/usr/bin/env python3
"""Search exact contextual folds of the published ZFC253 transition table.

Uses the upstream affine instruction checker as an executable experiment.
It does not claim a Coq build, a lower bound on all equivalent TMs, or a
correct blank bootstrap for a surviving runtime fold.  Every symbolic register
oracle row is protected.  A second mixed-row family combines the 0 action of
one state with the 1 action of the other before identifying the two states.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE / 'vendor' / 'busy-beaver'
PIN = '0d544f2a2e3c18f12278441a74b7879f31cbe856'
BOX_STATES = {0, 1, 2, 3, 4, 6, 28, 31, 38, 40, 43, 44, 48, 56, 59, 60,
              63, 64, 69, 73, 75, 83, 85, 95, 97, 109, 112, 131}
# The three return-state read-0 actions occur after the opaque file excursion
# has ended. In Box.v, ret_file qa qb assumes qb/1 but never qb/0. Its three
# instantiations are (1,3), (4,6), (63,48). The finite boundary actions below
# are handled by the ordinary symbolic executor, not by a box oracle.
BOX_PAIRS = {(str(q), b) for q in BOX_STATES for b in (0, 1)} - {
    ('3', 0), ('6', 0), ('48', 0)}


def load():
    candidate = REPO / 'ZF/m253/tools/generate_candidate.py'
    spec = importlib.util.spec_from_file_location('m253gen', candidate)
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    assert gen.generate_candidate() == (REPO / 'ZF/m253/machine/zfc_253.tm').read_bytes()
    table = {(str(q), b): (w, d, str(n))
             for (q, b), (w, d, n) in gen.patched_rows().items()}
    directory = REPO / 'ZF/m254/tools/tm'
    source = (directory / 'symexec.py').read_text().split('paths = json.load')[0]
    # Only the pinned public checker is executed; no user data is executed.
    sys.path.insert(0, str(directory))
    argv = sys.argv[:]
    sys.argv = ['symexec.py', str(REPO / 'ZF/m254/machine/zfc_254.tm'), '.', '40']
    env = {}
    exec(compile(source, str(directory / 'symexec.py'), 'exec'), env)
    sys.argv = argv
    body = (REPO / 'ZF/m253/coq/tm/Sites253.v').read_text()
    leaves = re.findall(r'\((\d+), (OInc|ODec|OBrk|OCont|OHalt)(?: (\d+))?\)', body)
    assert len(leaves) == 6460
    cases = []
    for code, operation, arg in leaves:
        path = bin(int(code))[3:]
        value = int(arg) if arg else None
        branches = [('z', 'dec0'), ('p', 'dec')] if operation == 'ODec' else [('-', 'inc' if operation == 'OInc' else None)]
        for branch, effect in branches:
            if operation == 'OInc' or operation == 'ODec' and branch == 'p':
                successor = env['inc'](path)
            elif operation == 'ODec':
                successor = env['inc'](env['strip']('0', 1, path))
            elif operation == 'OCont':
                successor = env['strip']('1', value, path)
            elif operation == 'OBrk':
                successor = env['inc'](env['strip']('0', value, path))
            else:
                successor = ''
            effects = () if effect is None else ((effect, value),)
            target = (env['canon']([('b', 1)], [('r', 0, 1, 41), ('b', 1), ('box', ('plain',) + effects)])
                      if successor is None else
                      env['canon']([('b', 1)], env['tape_R'](successor, 0, effects)))
            cases.append((path, operation, branch, target))
    assert len(cases) == 8391
    return gen, table, env, cases


class TracingTable(dict):
    def __init__(self, table):
        super().__init__(table)
        self.used = set()
    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


class FoldedTable:
    def __init__(self, base, dead, kept, rows):
        self.base, self.dead, self.kept, self.rows = base, dead, kept, rows
    def __getitem__(self, key):
        q, bit = key
        if q == self.dead:
            raise KeyError(key)
        w, d, target = self.rows[bit] if q == self.kept else self.base[key]
        return w, d, self.kept if target == self.dead else target


def run_case(env, case, table, fuel):
    path, operation, branch, target = case
    env['T'] = table
    try:
        out = env['run']('96', [('b', 1)], env['tape_R'](path, 0, ()), branch, target, fuel=fuel)
    except env['Fail'] as error:
        message = str(error)
        if message == 'fuel':
            kind = 'symbolic_fuel_exhausted'
        elif message.startswith('peel '):
            kind = 'unsupported_symbolic_run_peel'
        elif message.startswith('box touched'):
            kind = 'unsupported_register_box_entry'
        elif message == 'right exterior':
            kind = 'unsupported_right_exterior'
        else:
            raise
        return False, fuel, kind
    except KeyError:
        return False, fuel, 'missing_transition'
    good = out[0] == ('halt' if operation == 'OHalt' else 'ok')
    return good, out[1], ('ok' if good else 'unexpected_halt_or_normal_exit')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=('single', 'mixed', 'both'), default='both')
    parser.add_argument('--output', type=Path, default=HERE / 'runtime-fold-results.json')
    parser.add_argument('--fuel', type=int, default=700)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('This audit requires assertions; do not use python -O/-OO')
    gen, table, env, cases = load()
    begin = time.monotonic()
    usage = collections.defaultdict(list)
    lengths = []
    for i, case in enumerate(cases):
        traced = TracingTable(table)
        good, steps, _ = run_case(env, case, traced, args.fuel)
        assert good, ('baseline case failed', i, case[:3])
        lengths.append(steps)
        for q, b in traced.used:
            usage[q, b].append(i)
    for key in usage:
        usage[key].sort(key=lambda i: (lengths[i], i))
    states = sorted({q for q, _ in table}, key=int)
    protected = {str(q) for q in BOX_STATES | {96}}
    allowed = [q for q in states if q not in protected]
    # Thus redirecting a nonprotected state cannot change a protected box row.
    assert all(table[pair][2] in {str(q) for q in BOX_STATES} for pair in BOX_PAIRS)
    output = {'source_commit': PIN,
              'source_table_sha256': gen.CANDIDATE_SHA256,
              'state_labels': 'original254 labels, with state8 deleted',
              'baseline_affine_cases': len(cases),
              'baseline_maximum_abstract_steps': max(lengths),
              'gap_lower_bound': 40,
              'fuel_limit': args.fuel,
              'protected_box_states_and_dispatch': sorted(map(int, protected)),
              'protected_box_transition_pairs': [[int(q), b] for q, b in sorted(BOX_PAIRS, key=lambda p:(int(p[0]),p[1]))],
              'box_boundary_rows_checked_by_symbolic_executor': [[3,0],[6,0],[48,0]],
              'unread_nonbox_runtime_pairs': [[int(q), b] for q, b in table
                                              if q not in {str(x) for x in BOX_STATES}
                                              and (q, b) not in usage],
              'families': {},
              'kernel_build_reproduced': False,
              'blank_bootstrap_certified_for_new_candidates': False,
              'global_minimality_claimed': False}
    print('baseline 8391 cases PASS; starting folds', flush=True)
    def check(dead, kept, choices):
        rows = tuple(table[choices[b], b] for b in (0, 1))
        relevant = set(usage[dead, 0] + usage[dead, 1])
        for b in (0, 1):
            if rows[b] != table[kept, b]:
                relevant.update(usage[kept, b])
        candidate = FoldedTable(table, dead, kept, rows)
        ordered = sorted(relevant, key=lambda i: (lengths[i], i))
        for i in ordered:
            good, _, failure_kind = run_case(env, cases[i], candidate, args.fuel)
            if not good:
                return i, failure_kind
        return None, None
    families = ('single', 'mixed') if args.family == 'both' else (args.family,)
    for family in families:
        count, survivors, failures, reasons = 0, [], collections.Counter(), collections.Counter()
        if family == 'single':
            experiments = ((dead, kept, (kept, kept)) for dead in allowed for kept in states if dead != kept)
        else:
            experiments = ((dead, kept, choices)
                           for dead, kept in itertools.combinations(allowed, 2)
                           for choices in ((dead, kept), (kept, dead)))
        checkpoint = time.monotonic()
        for dead, kept, choices in experiments:
            failure, reason = check(dead, kept, choices)
            count += 1
            if failure is None:
                row = {'removed': int(dead), 'retained': int(kept),
                       'zero_row_from': int(choices[0]), 'one_row_from': int(choices[1])}
                survivors.append(row)
                print('SURVIVOR', row, flush=True)
            else:
                failures[failure] += 1
                reasons[reason] += 1
            if count % 10000 == 0:
                print(family, count, 'tried;', len(survivors), 'survivors;', round(time.monotonic() - checkpoint, 1), 'seconds', flush=True)
        output['families'][family] = {'attempts': count, 'survivors': survivors,
                                     'first_failing_cases_histogram': dict(sorted(failures.items())),
                                     'first_failure_reasons': dict(sorted(reasons.items())),
                                     'failures_are_rejected_certification_attempts_not_general_inequivalence_proofs': True,
                                     'elapsed_seconds': time.monotonic() - checkpoint}
        output['elapsed_seconds'] = time.monotonic() - begin
        args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
        print(family, 'DONE', count, 'attempts', len(survivors), 'survivors', flush=True)
    print('wrote', args.output, flush=True)


if __name__ == '__main__':
    main()
