#!/usr/bin/env python3
"""Bounded edge-specific deletion of old107 in the actual public253 table.

The original frontend is retained. Different incoming edges may target
different existing states, unlike the earlier uniform fold/fusion searches.
The attributed affine executor supplies diagnostic box summaries, not a
kernel proof. All imports and literal runs use fresh scratch copies.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter, defaultdict
import datetime
import hashlib
import json
from pathlib import Path
import platform
import shutil
import sys
import tempfile
import time

if not __debug__:
    raise SystemExit('Run without -O/-OO: checked contracts use assertions.')
sys.dont_write_bytecode = True


def assignment(path, name):
    tree = ast.parse(path.read_text())
    return next(ast.literal_eval(n.value) for n in tree.body
                if isinstance(n, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == name for t in n.targets))


def read_table(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = line.split()[-1]
        elif line and not line.startswith('#'):
            q, b, w, d, n = line.split()
            assert (q, int(b)) not in rows
            rows[q, int(b)] = int(w), d, n
    assert start is not None
    return rows, start


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--affine-fuel', type=int, default=1000)
    parser.add_argument('--boot-limit', type=int, default=400000)
    args = parser.parse_args()
    if min(args.affine_fuel, args.boot_limit) < 1:
        parser.error('fuel limits must be positive')
    repo = args.repo.resolve()
    host = repo / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
    work = Path(tempfile.mkdtemp(prefix='zfc-public253-context-'))
    for source, target in [
        ('04-machine-engineering-context_search.py', 'context_search.py'),
        ('04-machine-engineering-analyze_table.py', 'analyze_table.py'),
    ]:
        shutil.copyfile(host / 'code' / source, work / target)
    public = work / 'zfc_253.tm'
    shutil.copyfile(host / 'data/04-machine-machines-zfc_253.tm', public)
    sys.path.insert(0, str(work))
    import context_search as cs

    old = assignment(host / 'code/12-sorts-code-regenerate_253.py', 'OLD_LABELS')
    compact, initial = read_table(public)
    table = {(str(old[int(q)]), b): (w, d, str(old[int(n)]))
             for (q, b), (w, d, n) in compact.items()}
    start = str(old[int(initial)])
    assert hashlib.sha256(public.read_bytes()).hexdigest() == \
        '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'
    upstream = repo / 'lib/jeff-busy-beaver-zfc254/ZF/m254'
    base254, _ = read_table(upstream / 'machine/zfc_254.tm')
    reconstructed = {k: v for k, v in base254.items() if k[0] != '8'}
    reconstructed.update({('3', 0): (0, 'L', '48'), ('5', 0): (1, 'R', '97'),
                          ('5', 1): (1, 'R', '64'), ('49', 1): (0, 'R', '5')})
    assert table == reconstructed and start == '5' and len(table) == 506
    states = {q for q, b in table}
    assert len(states) == 253
    assert {k for k, row in table.items() if row[2] == '107'} == {('92', 0), ('130', 0)}
    assert table['107', 0] == table['104', 0] == table['129', 0] == (0, 'R', '121')
    box = assignment(host / 'code/20-complete-vendor-decoder255-verify.py', 'BOX_STATES')
    protected = {(str(q), b) for q in box for b in (0, 1)} - {('3', 0)}
    assert len(protected) == 55
    assert all(table[k] == base254[k] for k in protected)
    ns = cs.executor(table, upstream / 'tools/tm/symexec.py')
    cases = cs.cases(ns, cs.program_sites(upstream / 'coq/tm/Prog254.v'))
    assert len(cases) == 8391 and ns['D0'] == 40

    def check(current, index):
        _, path, op, _, branch, expected = cases[index]
        ns['T'] = current
        try:
            result = ns['run']('96', [('b', 1)], ns['tape_R'](path, 0, ()),
                               branch, expected, fuel=args.affine_fuel)
        except ns['Fail'] as error:
            return {'pass': False, 'reason': 'fuel_exhausted' if str(error) == 'fuel'
                    else 'symbolic_abstraction_limit', 'detail': str(error)}
        except KeyError as error:
            return {'pass': False, 'reason': 'missing_transition', 'detail': str(error)}
        if result[0] != ('halt' if op == 'CH' else 'ok'):
            return {'pass': False, 'reason': 'unexpected_status', 'detail': list(result)}
        return {'pass': True, 'abstract_steps': result[1]}

    physical = [0, 2, 0, 0, 0, 0, 5, 0, 0]
    spares = [0, 0, 1, 0, 0, 0, 0, 0, 1] + [0] * 149
    target_head = -17
    target_ones = {target_head - 1, target_head + 40}
    pos = target_head + 41
    for value in physical + spares:
        pos += 1
        target_ones.update(range(pos, pos + value + 1))
        pos += value + 1
    assert len(spares) == 158 and len(target_ones) == 178

    def blank_run(current, limit):
        q, head, ones = start, 0, set()
        for steps in range(limit + 1):
            if q == '96' and head == target_head and ones == target_ones:
                return {'outcome': 'exact_target', 'steps': steps, 'state': q,
                        'head': head, 'ones': len(ones), 'whole_tape_equal': True}
            if q == '254':
                return {'outcome': 'halt', 'steps': steps, 'head': head, 'ones': len(ones)}
            if steps == limit:
                return {'outcome': 'fuel_limit', 'steps': steps, 'state': q,
                        'head': head, 'ones': len(ones)}
            w, direction, q = current[q, int(head in ones)]
            if w:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if direction == 'R' else -1

    usage = defaultdict(set)
    edge_bits = defaultdict(set)
    edge_cases = defaultdict(set)
    previous = [None]
    current_index = [None]

    class Tracking(dict):
        def __getitem__(self, key):
            usage[key].add(current_index[0])
            if previous[0] is not None and table[previous[0]][2] == key[0]:
                edge_bits[previous[0]].add(key[1])
                edge_cases[previous[0], key[1]].add(current_index[0])
            previous[0] = key
            return super().__getitem__(key)

    begin = time.monotonic()
    baseline_steps = {}
    traced = Tracking(table)
    for i in range(len(cases)):
        previous[0], current_index[0] = None, i
        checked = check(traced, i)
        assert checked['pass'], (i, checked)
        baseline_steps[i] = checked['abstract_steps']
    baseline_boot = blank_run(table, 312975)
    assert baseline_boot['outcome'] == 'exact_target' and baseline_boot['steps'] == 312975
    assert edge_bits['92', 0] == {0} and edge_bits['130', 0] == {0, 1}
    affected = set().union(*(usage[k] for k in [('92', 0), ('130', 0), ('107', 0), ('107', 1)]))
    affected = sorted(affected, key=lambda i: (baseline_steps[i], i))
    output = args.output.resolve() if args.output else work / 'results.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {
        'status': 'running', 'scratch': str(work),
        'scope': 'Bounded edge-specific old107 deletion, original full frontend; '
                 'attributed affine box summaries, no kernel proof or minimality claim.',
        'attribution': 'Mira-Cult original machine; Jeff verification/affine executor; '
                       'mira-emmy public253 reduction; Wade TMBuilder; source04/source09 helpers.',
        'public_pin': '0d544f2a2e3c18f12278441a74b7879f31cbe856',
        'table_sha256': hashlib.sha256(public.read_bytes()).hexdigest(),
        'table_four_edit_identity_checked': True,
        'driver_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'python': platform.python_version(),
        'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'baseline_affine_cases_passed': len(cases), 'baseline_exact_boot': baseline_boot,
        'baseline_affected_cases': len(affected), 'affine_fuel': args.affine_fuel,
        'boot_limit': args.boot_limit, 'gap_lower_bound': 40,
        'candidate_working_states': 252, 'candidate_rows': 504,
        'candidate_start_old': 5, 'candidate_halt_old': 254,
        'recipes': 504, 'nonuniform_recipes': 502, 'uniform_controls': 2,
        'protected_pairs': sorted([list(k) for k in protected], key=lambda k: (int(k[0]), k[1])),
        'guard_census': {f'{q}/{b}': {str(bit): len(edge_cases[(q, b), bit])
                                   for bit in sorted(edge_bits[q, b])}
                         for q, b in [('92', 0), ('130', 0)]},
        'target': {'old_state': 96, 'head': target_head, 'physical_primary': physical,
                   'spares': spares, 'entire_tape_ones': sorted(target_ones)},
        'candidates': [], 'affine_survivors': [], 'exact_boot_survivors': [],
    }

    def save():
        result['elapsed_seconds'] = time.monotonic() - begin
        output.write_text(json.dumps(result, indent=2) + '\n')

    save()
    print('BASELINE PASS8391; exact boot312975; protected55; affected', len(affected), flush=True)
    for surrogate in ('104', '129'):
        for replacement in sorted(states - {'107'}, key=int):
            candidate = {k: v for k, v in table.items() if k[0] != '107'}
            candidate['92', 0] = 0, 'L', surrogate
            candidate['130', 0] = 0, 'R', replacement
            assert len(candidate) == 504 and len({q for q, b in candidate}) == 252
            assert all(candidate[k] == table[k] for k in protected)
            assert {n for w, d, n in candidate.values()} <= states - {'107'} | {'254'}
            row = {'surrogate_92': surrogate, 'replacement_130': replacement,
                   'uniform_control': surrogate == replacement,
                   'protected_pairs_unchanged': 55, 'affine_checks': 0}
            for index in affected:
                checked = check(candidate, index)
                row['affine_checks'] += 1
                if not checked['pass']:
                    row['outcome'] = 'rejected_affected'
                    row['first_failure'] = {'case': index, 'site': list(cases[index][:-1]), **checked}
                    break
            else:
                for index in range(len(cases)):
                    checked = check(candidate, index)
                    row['affine_checks'] += 1
                    if not checked['pass']:
                        row['outcome'] = 'rejected_full_recheck'
                        row['first_failure'] = {'case': index, 'site': list(cases[index][:-1]), **checked}
                        break
                else:
                    row['outcome'] = 'all8391_passed'
                    result['affine_survivors'].append([surrogate, replacement])
                    row['blank_run'] = blank_run(candidate, args.boot_limit)
                    print('AFFINE SURVIVOR', surrogate, replacement, row['blank_run'], flush=True)
                    if row['blank_run']['outcome'] == 'exact_target':
                        result['exact_boot_survivors'].append([surrogate, replacement])
                        artifact = work / f'candidate-107-{surrogate}-{replacement}.tm'
                        artifact.write_text('#! start 5\n' + ''.join(
                            f'{q} {b} {w} {d} {n}\n' for (q, b), (w, d, n) in
                            sorted(candidate.items(), key=lambda x: (int(x[0][0]), x[0][1]))))
                        row['table_artifact'] = str(artifact)
            result['candidates'].append(row)
        save()
        print('SURROGATE DONE', surrogate, 'candidates', len(result['candidates']), flush=True)
    assert len(result['candidates']) == 504
    assert sum(r['uniform_control'] for r in result['candidates']) == 2
    result['status'] = 'completed'
    result['outcomes'] = dict(Counter(r['outcome'] for r in result['candidates']))
    result['rejection_reasons'] = dict(Counter(r['first_failure']['reason']
                                               for r in result['candidates'] if 'first_failure' in r))
    result['finite_fuel_or_abstraction_failure_is_not_impossibility'] = True
    result['no_goal_endpoint_claimed'] = True
    save()
    print(json.dumps({k: result[k] for k in ['status', 'outcomes', 'rejection_reasons',
                                           'affine_survivors', 'exact_boot_survivors',
                                           'elapsed_seconds']}, indent=2), flush=True)
    print('Evidence:', output, flush=True)


if __name__ == '__main__':
    main()
