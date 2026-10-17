#!/usr/bin/env python3
"""Bounded two-incoming-edge deletions of the frozen permutation252 table.

Each incoming row is first redirected separately, retaining the old state.
The retained domains are then combined, the old state is removed, and every
joint survivor receives all8391 affine cases before an actual blank run.
This sufficient domain restriction excludes jointly compensating rewrites
that fail separately. A negative result is neither minimality nor nonhalting.
The55 protected register-box rows, dispatch96 and blank start64 stay fixed.
The symbolic macro contracts are diagnostic; modified tables receive no Lean
proof here. No Lean/Coq process, network request or frozen-table edit occurs.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import platform
import re
import sys
import tempfile
import time
from types import SimpleNamespace

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]


class Tracking(dict):
    def __init__(self, rows):
        super().__init__(rows)
        self.used = set()

    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--scratch', type=Path)
    parser.add_argument('--seconds', type=float, default=120)
    parser.add_argument('--affine-fuel', type=int, default=1000)
    parser.add_argument('--boot-limit', type=int, default=1000000)
    parser.add_argument('--joint-limit', type=int, default=100000)
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must remain enabled')
    if min(args.seconds, args.affine_fuel, args.boot_limit, args.joint_limit) <= 0:
        parser.error('Positive bounds required')
    repo = args.repo.resolve()
    base = repo / 'Computability/BusyBeaver/Research/ZFC'
    work = args.scratch.resolve() if args.scratch else Path(tempfile.mkdtemp(prefix='zfc-perm252-context-'))
    if work == repo or repo in work.parents:
        parser.error('External scratch required')
    work.mkdir(parents=True, exist_ok=True)
    audit = load('permutation252_context_audit', base / 'candidate252_independent_audit.py')
    frozen = base / 'candidate-permutation252/zfc_permutation252_old.tm'
    raw = frozen.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == audit.EXPECTED_SHA
    numeric = audit.read_table(raw)
    table = {(str(q), b): (v, d, str(t)) for (q, b), (v, d, t) in numeric.items()}
    states = sorted({q for q, b in table}, key=int)
    protected = {(str(q), b) for q, b in audit.BOX_PAIRS}
    assert len(states) == 252 and len(table) == 504 and len(protected) == 55
    strict_source = repo / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    (work / 'strict_affine.py').write_bytes(strict_source.read_bytes())
    sys.modules['cost_search'] = SimpleNamespace()
    strict = load('permutation252_context_strict', work / 'strict_affine.py')
    prog = repo / 'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    text = prog.read_text().split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', text)
    assert len(nodes) == 6459
    cases = []

    def visit(q, prefix):
        for b, e in enumerate(nodes[q]):
            path = prefix + str(b)
            op, *arg = e.split()
            if op == 'CN':
                visit(int(arg[0]), path)
                continue
            register = int(arg[0]) if arg else None
            for zero in ((True, False) if op == 'CD' else (None,)):
                physical = audit.NEWPHYS[register] if op in ('CI', 'CD') else register
                branch = (physical, zero) if op == 'CD' else None
                successor = audit.successor(path, op, register, zero)
                effect = ('inc', physical) if op == 'CI' else ('dec', physical) if op == 'CD' and not zero else None
                right = [('b', int(c)) for c in successor] if successor is not None else []
                right += [('r', 0, 1, (41 if successor is None else 40) - len(successor or '')),
                          ('b', 1), ('box', ('plain', effect))]
                cases.append((path, op, register, zero, branch, strict.canon([('b', 1)], right)))

    visit(0, '')
    assert len(cases) == 8391

    def check(current, index):
        path, op, register, zero, branch, target = cases[index]
        try:
            rules, literal = strict.run(current, path, branch, target, halt=op == 'CH', fuel=args.affine_fuel)
            assert literal > 0
            return True, sum(rules.values()), None
        except AssertionError as exc:
            return False, 0, 'fuel' if str(exc) == 'symbolic fuel exhausted' else 'unsupported_symbolic_rule'
        except KeyError:
            return False, 0, 'missing_transition'

    began = time.monotonic()
    usage = defaultdict(set)
    baseline_cost = {}
    for index in range(len(cases)):
        traced = Tracking(table)
        ok, cost, _ = check(traced, index)
        assert ok, ('baseline_case', index)
        baseline_cost[index] = cost
        for row in traced.used:
            usage[row].add(index)
    target_spares = [0] * 65
    target_spares[8] = 1
    target_ones = audit.paint('', 40, [0] * 9, target_spares, 2)
    q, h, ones, _, _ = audit.run_prefix(numeric, 82552)
    assert (q, h, ones) == (96, 2, target_ones)
    protected_targets = {table[k][2] for k in protected}
    eligible = [q for q in states if q not in {'64', '96'} and q not in protected_targets
                and all((q, b) not in protected for b in (0, 1))]
    incoming = {q: sorted([k for k, (_, _, t) in table.items() if t == q and k[0] != q],
                          key=lambda k: (int(k[0]), k[1])) for q in eligible}
    family = [q for q in eligible if len(incoming[q]) == 2]
    assert len(family) == 46 and all(usage[k] for q in family for k in incoming[q])
    # old107's two distinct guards motivated the previous public253 experiment.
    family.sort(key=lambda q: (q != '107', int(q)))
    out = args.output.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    result = {
        'status': 'running',
        'scope': 'Sufficient-domain two-incoming-edge251-state deletion diagnostics; no minimality, consistency or kernel proof of modified tables.',
        'attribution': 'Mira-Cult/Jeff/Wade original254; mira-emmy public253 PR20; frozen physical-register permutation252; strict affine executor retained from source27.',
        'table': str(frozen.relative_to(repo)), 'table_sha256': audit.EXPECTED_SHA,
        'logical_to_physical': list(audit.NEWPHYS), 'working_states': 252, 'protected_pairs': 55,
        'fixed_old_dispatch': 96, 'fixed_old_blank_start': 64,
        'baseline_affine_cases': 8391, 'baseline_exact82552_whole_boot': 'PASS',
        'eligible_two_external_incoming_states': list(map(int, family)),
        'planned_single_row_screens': 46 * 2 * 251,
        'single_row_semantics': 'State retained; alter only the named incoming target. Affected cases are every baseline actual table lookup of that row; all remaining baseline traces are unchanged.',
        'joint_semantics': 'Combine independently passing targets, delete both rows of the old state; skip equal-target assignments already rejected by the uniform fold search. Recheck all8391 before any blank run.',
        'restriction': 'Jointly compensating assignments that fail one-row screening are excluded. Fuel or unsupported rules are finite diagnostic rejections, not mathematical impossibility.',
        'macro_contracts': 'Four register-box excursions; all55 supporting literal rows fixed. Candidate modified decoder tables are not kernel-certified here.',
        'affine_fuel': args.affine_fuel, 'boot_limit': args.boot_limit,
        'seconds_limit': args.seconds, 'joint_limit': args.joint_limit,
        'command': [sys.executable, *sys.argv], 'python': platform.python_version(), 'scratch': str(work),
        'input_sha256': {'driver': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                         'audit_helper': hashlib.sha256((base / 'candidate252_independent_audit.py').read_bytes()).hexdigest(),
                         'strict_executor': hashlib.sha256(strict_source.read_bytes()).hexdigest(),
                         'Prog254': hashlib.sha256(prog.read_bytes()).hexdigest()},
        'completed_single_screens': 0, 'completed_joint_assignments': 0,
        'single_affine_checks': 0, 'joint_affine_checks': 0, 'full_recheck_affine_checks': 0,
        'skipped_uniform_assignments': 0, 'states': [], 'affine_survivors': [], 'whole_boot_survivors': []}
    failures = Counter()
    stopped = False

    def save():
        result['elapsed_seconds'] = time.monotonic() - began
        result['failure_reasons'] = dict(failures)
        out.write_text(json.dumps(result, indent=2) + '\n')

    def ordered(indices):
        return sorted(indices, key=lambda i: (baseline_cost[i], i))

    def blank_run(candidate):
        state, head, tape = '64', 0, set()
        for tick in range(args.boot_limit + 1):
            if state == '96' and head == 2 and tape == target_ones:
                return {'outcome': 'exact_frozen_whole_frame', 'steps': tick}
            if state == '254':
                return {'outcome': 'halt', 'steps': tick}
            if tick == args.boot_limit:
                return {'outcome': 'fuel_limit', 'steps': tick}
            write, direction, state = candidate[state, int(head in tape)]
            if write:
                tape.add(head)
            else:
                tape.discard(head)
            head += 1 if direction == 'R' else -1

    save()
    print('BASELINE8391+exact82552 PASS;46 states/23092 single-row screens', flush=True)
    journal = work / 'screens.jsonl'
    with journal.open('w') as record:
        for dead in family:
            row_keys = incoming[dead]
            group = {'deleted_old': int(dead), 'incoming_rows': [list(k) for k in row_keys],
                     'row_domains': [], 'single_screens': 0, 'joint_assignments': 0}
            result['states'].append(group)
            for row in row_keys:
                domain = []
                row_failures = []
                for destination in states:
                    if destination == dead:
                        continue
                    if time.monotonic() - began >= args.seconds:
                        stopped = True
                        break
                    candidate = dict(table)
                    write, direction, _ = candidate[row]
                    candidate[row] = write, direction, destination
                    assert all(candidate[k] == table[k] for k in protected)
                    failed, reason = None, None
                    for index in ordered(usage[row]):
                        ok, _, reason = check(candidate, index)
                        result['single_affine_checks'] += 1
                        if not ok:
                            failed = index
                            break
                    if failed is None:
                        domain.append(destination)
                    else:
                        failures['single_' + reason] += 1
                    record.write(json.dumps({'deleted': int(dead), 'incoming': list(row),
                                             'destination': int(destination), 'first_failure': failed,
                                             'reason': reason}, separators=(',', ':')) + '\n')
                    row_failures.append(failed)
                    result['completed_single_screens'] += 1
                    group['single_screens'] += 1
                group['row_domains'].append({'incoming': list(row), 'affected_cases': len(usage[row]),
                                             'destinations': list(map(int, domain)),
                                             'first_failure_in_destination_order': row_failures})
                if stopped:
                    break
            save()
            if stopped:
                break
            domains = [[str(q) for q in d['destinations']] for d in group['row_domains']]
            group['cartesian_product_size'] = len(domains[0]) * len(domains[1])
            for destinations in itertools.product(*domains):
                if destinations[0] == destinations[1]:
                    result['skipped_uniform_assignments'] += 1
                    continue
                if time.monotonic() - began >= args.seconds or result['completed_joint_assignments'] >= args.joint_limit:
                    stopped = True
                    break
                candidate = {k: v for k, v in table.items() if k[0] != dead}
                for row, destination in zip(row_keys, destinations):
                    write, direction, _ = candidate[row]
                    candidate[row] = write, direction, destination
                assert len(candidate) == 502 and all(candidate[k] == table[k] for k in protected)
                assert all(t != dead for _, _, t in candidate.values())
                failed, reason = None, None
                for index in ordered(set.union(*(usage[k] for k in row_keys))):
                    ok, _, reason = check(candidate, index)
                    result['joint_affine_checks'] += 1
                    if not ok:
                        failed = index
                        break
                if failed is None:
                    for index in range(len(cases)):
                        ok, _, reason = check(candidate, index)
                        result['full_recheck_affine_checks'] += 1
                        if not ok:
                            failed = index
                            break
                entry = {'deleted_old': int(dead), 'incoming_rows': [list(k) for k in row_keys],
                         'destinations': list(map(int, destinations)), 'first_failure_case': failed, 'reason': reason}
                if failed is None:
                    data = ('#! start 64\n' + ''.join(
                        f'{q} {b} {v} {d} {t}\n' for (q, b), (v, d, t) in sorted(
                            candidate.items(), key=lambda item: (int(item[0][0]), item[0][1])))).encode()
                    path = work / f'context_{dead}_{destinations[0]}_{destinations[1]}.tm'
                    path.write_bytes(data)
                    entry.update({'table': str(path), 'table_sha256': hashlib.sha256(data).hexdigest(),
                                  'boot': blank_run(candidate)})
                    result['affine_survivors'].append(entry)
                    print('AFFINE SURVIVOR', json.dumps(entry), flush=True)
                    if entry['boot']['outcome'] == 'exact_frozen_whole_frame':
                        result['whole_boot_survivors'].append(entry)
                else:
                    failures['joint_' + reason] += 1
                record.write(json.dumps(entry, separators=(',', ':')) + '\n')
                result['completed_joint_assignments'] += 1
                group['joint_assignments'] += 1
            record.flush()
            save()
            if stopped:
                break
    result['status'] = 'bound_partial' if stopped else 'completed'
    if not stopped:
        assert result['completed_single_screens'] == 23092
    result['journal'] = {'path': str(journal), 'sha256': hashlib.sha256(journal.read_bytes()).hexdigest(),
                         'bytes': journal.stat().st_size}
    save()
    print(json.dumps({k: result[k] for k in ('status', 'completed_single_screens', 'completed_joint_assignments',
                                            'affine_survivors', 'whole_boot_survivors', 'elapsed_seconds')}), flush=True)


if __name__ == '__main__':
    main()
