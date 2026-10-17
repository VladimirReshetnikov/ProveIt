#!/usr/bin/env python3
"""Bounded mixed-row fusions in source27's four-row faster253 variant.

The three newly reassociated decoder states are the only deletion sources.
Uniform folds were already searched by source27; this search keeps exactly
one row from each fusion parent, plus six both-row frontier recipes omitted
by that earlier search's literal-row protection.  Baseline strict8391 and complete312935-step
boot checks precede every candidate.  No Lean/Coq build, network fetch, source
mutation, consistency endpoint or minimality claim is involved.
"""

from __future__ import annotations

import argparse
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


def read_table(path):
    table, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = line.split()[-1]
        elif line and not line.startswith('#'):
            q, b, w, d, t = line.split()
            key = q, int(b)
            assert key not in table and key[1] in (0, 1)
            assert int(w) in (0, 1) and d in ('L', 'R')
            table[key] = int(w), d, t
    assert start is not None
    states = {q for q, _ in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    return table, start


def quotient_profile(table, halt):
    states = sorted({q for q, _ in table}, key=int)
    assert halt not in states
    classes = {q: 0 for q in states}
    counts = [1]
    while True:
        signatures = {q: tuple((w, d, -1 if t == halt else classes[t])
                               for w, d, t in (table[q, 0], table[q, 1]))
                      for q in states}
        labels = {}
        new = {q: labels.setdefault(signatures[q], len(labels)) for q in states}
        counts.append(len(labels))
        if all((classes[a] == classes[b]) == (new[a] == new[b])
               for a in states for b in states):
            groups = defaultdict(list)
            for q in states:
                groups[new[q]].append(q)
            return {'working_class_counts': counts,
                    'nontrivial_classes': [v for v in groups.values() if len(v) > 1]}
        classes = new


def fuse(table, deleted, retained, mask):
    """Redirect all incoming targets, choosing bit b from deleted iff mask[b]."""
    assert mask in (1, 2, 3) and deleted != retained
    result = {}
    for (q, b), row in table.items():
        if q == deleted:
            continue
        if q == retained and mask & (1 << b):
            row = table[deleted, b]
        w, d, target = row
        result[q, b] = w, d, retained if target == deleted else target
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--affine-fuel', type=int, default=1000)
    parser.add_argument('--boot-limit', type=int, default=400000)
    parser.add_argument('--baseline-only', action='store_true')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must remain enabled')
    if args.affine_fuel < 1 or args.boot_limit < 312935:
        parser.error('Positive affine fuel and boot limit at least312935 required')
    repo = args.repo.resolve()
    host = repo / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
    work = Path(tempfile.mkdtemp(prefix='zfc-variant253-fusion-'))
    grammar = work / 'grammar_search'
    grammar.mkdir()
    modules = ('cost_search', 'rotate_search', 'dag_tools', 'prior_context_search',
               'analyze_table', 'prior_rm_verify', 'strict_affine')
    for name in modules:
        shutil.copyfile(host / f'code/27-variant-experiments-machine_search-grammar_search-{name}.py',
                        grammar / (name + '.py'))
    shutil.copyfile(host / 'data/27-variant-experiments-machine_search-grammar_search-decoder_entries.json',
                    grammar / 'decoder_entries.json')
    for relative in ('ZF/m254/machine/zfc_254.tm', 'ZF/m253/machine/zfc_253.tm',
                     'ZF/m254/coq/tm/Prog254.v', 'ZF/m254/tools/tm/symexec.py',
                     'ZF/m254/tools/tm/tmlib.py'):
        stem = relative.replace('/', '-')
        extension = 'data' if relative.endswith('.tm') else 'code'
        target = work / 'upstream253' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(host / extension / ('27-variant-experiments-machine_search-upstream253-' + stem), target)
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(grammar))
    import cost_search as source
    import strict_affine as strict

    compact_path = host / 'data/27-variant-machines-faster_253.tm'
    compact, start_compact = read_table(compact_path)
    original, original_start = read_table(host / 'data/27-variant-machines-upstream_253.tm')
    mapping = json.loads((host / 'data/27-variant-experiments-machine_search-grammar_search-candidate-state_map.json').read_text())['old_of_compact']
    assert len(mapping) == 254 and mapping[0] == 5 and mapping[33] == 96 and mapping[253] == 254
    assert set(compact) == {(str(q), b) for q in range(253) for b in (0, 1)}
    assert start_compact == original_start == '0'
    delta = [{'state': int(q), 'read': b, 'before': list(original[q, b]), 'after': list(row)}
             for (q, b), row in compact.items() if original[q, b] != row]
    assert {(x['state'], x['read'], int(x['after'][2])) for x in delta} == {
        (37, 0, 42), (37, 1, 48), (42, 0, 41), (42, 1, 50)}
    assert len(delta) == 4 and all(x['before'][:2] == x['after'][:2] for x in delta)
    table = {(str(mapping[int(q)]), b): (w, d, str(mapping[int(t)]))
             for (q, b), (w, d, t) in compact.items()}
    start, halt = '5', '254'
    states = {q for q, _ in table}
    assert len(states) == 253 and {t for _, _, t in table.values()} <= states | {halt}
    n, edge, kind = source.rot.options(source.NODES)[0]
    assert n == 7 and kind == 'associate_left'
    nodes, root = source.rot.mutate(source.NODES, source.ROOT, n, edge)
    reconstructed = source.emit(nodes, root)
    assert all(reconstructed[key] == row for key, row in table.items())
    protected = source.BOX_PAIRS
    assert len(protected) == 55 and all(table[key] == source.BASE253[key] for key in protected)
    assert all(table['5', b] == source.BASE253['5', b] for b in (0, 1))
    proto = source.ctx.executor(table, source.BASE / 'tools/tm/symexec.py')
    cases = []
    for pc, operation, register in source.sites(nodes, root):
        for zero in ((True, False) if operation == 'CD' else (None,)):
            branch = (register, zero) if zero is not None else None
            if operation == 'CI' or (operation == 'CD' and not zero):
                successor = proto['inc'](pc)
            elif operation == 'CD':
                successor = proto['inc'](proto['strip']('0', 1, pc))
            elif operation == 'CB':
                successor = proto['inc'](proto['strip']('0', register, pc))
            elif operation == 'CC':
                successor = proto['strip']('1', register, pc)
            else:
                successor = ''
            effect = (('inc', register) if operation == 'CI' else
                      ('dec', register) if operation == 'CD' and not zero else None)
            if successor is None:
                right = [('r', 0, 1, 41), ('b', 1), ('box', ('plain', effect))]
            else:
                right = [('b', int(bit)) for bit in successor]
                right += [('r', 0, 1, 40 - len(successor)), ('b', 1), ('box', ('plain', effect))]
            cases.append((pc, operation, register, branch, strict.canon([('b', 1)], right)))
    assert len(cases) == 8391

    def check(current, index):
        pc, operation, register, branch, target = cases[index]
        try:
            rules, literal = strict.run(current, pc, branch, target,
                                        halt=operation == 'CH', fuel=args.affine_fuel)
            assert literal > 0
            return {'pass': True, 'symbolic_rules': sum(rules.values()), 'literal_rules': literal}
        except AssertionError as exc:
            message = str(exc)
            reason = ('fuel' if message == 'symbolic fuel exhausted' else
                      'unsupported_symbolic_rule')
            return {'pass': False, 'reason': reason, 'message': message}
        except KeyError as exc:
            missing = exc.args[0]
            return {'pass': False, 'reason': 'unexpected_halt' if missing[0] == halt else 'missing_row',
                    'message': repr(missing)}

    physical = [0, 2, 0, 0, 0, 0, 5, 0, 0]
    spares = [0, 0, 1, 0, 0, 0, 0, 0, 1] + [0] * 149
    target_head = -17
    target_ones = {target_head - 1, target_head + 40}
    position = target_head + 41
    for value in physical + spares:
        position += 1
        target_ones.update(range(position, position + value + 1))
        position += value + 1
    assert len(spares) == 158 and len(target_ones) == 178

    def prefix(current, steps):
        q, head, ones = start, 0, set()
        used = set()
        for _ in range(steps):
            key = q, int(head in ones)
            used.add(key)
            w, direction, q = current[key]
            if w:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if direction == 'R' else -1
        return q, head, ones, used

    def boot_candidate(current):
        q, head, ones = start, 0, set()
        for steps in range(args.boot_limit + 1):
            if q == '96' and head == target_head and ones == target_ones:
                return {'outcome': 'exact_target', 'steps': steps, 'whole_tape_equal': True}
            if q == halt:
                return {'outcome': 'halt', 'steps': steps, 'head': head}
            if steps == args.boot_limit:
                return {'outcome': 'fuel_limit', 'steps': steps, 'state': q,
                        'head': head, 'ones': len(ones)}
            w, direction, q = current[q, int(head in ones)]
            if w:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if direction == 'R' else -1

    usage = defaultdict(set)
    active_index = [None]

    class Tracking(dict):
        def __getitem__(self, key):
            usage[key].add(active_index[0])
            return super().__getitem__(key)

    begin = time.monotonic()
    baseline = []
    traced = Tracking(table)
    for index in range(len(cases)):
        active_index[0] = index
        answer = check(traced, index)
        assert answer['pass'], (index, answer)
        baseline.append(answer)
    q, head, ones, boot_rows = prefix(table, 312935)
    assert (q, head, ones) == ('96', target_head, target_ones)
    profile = quotient_profile(table, halt)
    assert not profile['nontrivial_classes'] and profile['working_class_counts'][-1] == 253
    deletion_sources = ('255', '256', '257')
    excluded_retained = {str(q) for q in source.BOX_STATES} | {'5', '96'}
    destinations = sorted(states - excluded_retained, key=int)
    recipes = [(deleted, retained, mask) for deleted in deletion_sources
               for retained in destinations if retained != deleted for mask in (1, 2)]
    # Inverse uniform folds deleting these two frontier labels were excluded
    # by source27's literal protected-row test.  Keeping the frontier label and
    # copying both new rows preserves all55 protected rows, so these six are
    # distinct from that earlier tested family despite an inverse renaming.
    frontier = sorted(({table[key][2] for key in protected} - excluded_retained) &
                      set(destinations), key=int)
    assert frontier == ['7', '9']
    recipes += [(deleted, retained, 3) for deleted in deletion_sources for retained in frontier]
    output = args.output.resolve() if args.output else work / 'results.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {
        'status': 'baseline_passed', 'scratch': str(work),
        'scope': 'Strict affine mixed-row diagnostic with unchanged55 register-box rows; no kernel proof, consistency endpoint or global minimality claim.',
        'attribution': 'Source27 faster253 reassociation; Mira-Cult/Jeff/Wade/mira-emmy machine lineage; source27 strict port and source04/source09 helpers.',
        'source_archive_commit': 'da6dabcd8976acf94c4f3652ed3eeae5713b3d2a',
        'public253_pin': '0d544f2a2e3c18f12278441a74b7879f31cbe856',
        'variant_table': str(compact_path.relative_to(repo)),
        'variant_table_sha256': hashlib.sha256(compact_path.read_bytes()).hexdigest(),
        'compact_delta': delta, 'renamed_old_labels': {'12': 255, '128': 256, '110': 257},
        'baseline_cases': len(cases), 'baseline_cases_all_passed': True,
        'baseline_minimum_literal_rules': min(x['literal_rules'] for x in baseline),
        'baseline_exact_boot': {'steps': 312935, 'old_state': q, 'head': head,
                                'ones': len(ones), 'whole_tape_equal': True,
                                'first_arrival_claimed': False},
        'target': {'head': target_head, 'physical_primary': physical, 'spares': spares,
                   'all_one_positions': sorted(target_ones), 'all_other_cells_zero': True},
        'exact_quotient': profile, 'affine_fuel': args.affine_fuel,
        'candidate_boot_limit': args.boot_limit, 'candidate_working_states': 252,
        'deletion_sources': list(deletion_sources), 'excluded_retained_states': sorted(excluded_retained, key=int),
        'planned_recipes': len(recipes), 'mixed_masks': [1, 2],
        'mixed_recipes': len(recipes) - 6,
        'inverse_fold_frontier_retained': frontier, 'inverse_fold_frontier_recipes': 6,
        'uniform_mask0_omitted_as_prior_search': True,
        'remaining_mask3_omitted_as_inverse_prior_folds': True,
        'baseline_source_usage': {p: len(set().union(*(usage[p, b] for b in (0, 1))))
                                  for p in deletion_sources},
        'baseline_source_rows_used_in_boot': {p: sorted(b for b in (0, 1) if (p, b) in boot_rows)
                                             for p in deletion_sources},
        'python': platform.python_version(), 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'candidates': [], 'affine_survivors': [], 'boot_survivors': [],
    }

    def save():
        result['elapsed_seconds'] = time.monotonic() - begin
        output.write_text(json.dumps(result, indent=2) + '\n')

    save()
    print('BASELINE PASS8391, exact whole boot312935, exact quotient253; recipes', len(recipes), flush=True)
    if args.baseline_only:
        print('Evidence:', output, flush=True)
        return
    for deleted, retained, mask in recipes:
        candidate = fuse(table, deleted, retained, mask)
        assert len(candidate) == 504 and {t for _, _, t in candidate.values()} <= states - {deleted} | {halt}
        assert all(candidate[key] == table[key] for key in protected)
        assert all(candidate['5', b] == table['5', b] for b in (0, 1))
        changed = [key for key, row in candidate.items() if row != table[key]]
        affected = set().union(*(usage[key] for key in changed), *(usage[deleted, b] for b in (0, 1)))
        affected = sorted(affected, key=lambda i: (baseline[i]['symbolic_rules'], i))
        record = {'deleted': deleted, 'retained': retained, 'mask': mask,
                  'recipe_kind': 'mixed_rows' if mask != 3 else 'inverse_fold_protected_frontier',
                  'changed_rows': [{'state': key[0], 'read': key[1],
                                    'before': list(table[key]), 'after': list(candidate[key])}
                                   for key in changed],
                  'affected_cases': len(affected), 'case_checks': 0}
        for index in affected:
            answer = check(candidate, index)
            record['case_checks'] += 1
            if not answer['pass']:
                record['outcome'] = 'rejected_affected'
                record['failure'] = {'index': index, 'path': cases[index][0],
                                     'operation': cases[index][1], 'branch': cases[index][3], **answer}
                break
        else:
            for index in range(len(cases)):
                answer = check(candidate, index)
                record['case_checks'] += 1
                if not answer['pass']:
                    record['outcome'] = 'rejected_full_recheck'
                    record['failure'] = {'index': index, **answer}
                    break
            else:
                record['outcome'] = 'all8391_passed'
                result['affine_survivors'].append([deleted, retained, mask])
                record['boot'] = boot_candidate(candidate)
                if record['boot']['outcome'] == 'exact_target':
                    result['boot_survivors'].append([deleted, retained, mask])
                    artifact = work / f'fusion-{deleted}-{retained}-{mask}.tm'
                    artifact.write_text('#! start 5\n' + ''.join(
                        f'{p} {b} {w} {d} {t}\n' for (p, b), (w, d, t) in
                        sorted(candidate.items(), key=lambda row: (int(row[0][0]), row[0][1]))))
                    record['artifact'] = str(artifact)
                print('AFFINE SURVIVOR', deleted, retained, mask, record['boot'], flush=True)
        result['candidates'].append(record)
        if len(result['candidates']) % 250 == 0:
            save()
            print('CHECKED', len(result['candidates']), '/', len(recipes), flush=True)
    result['status'] = 'completed'
    result['outcomes'] = dict(Counter(row['outcome'] for row in result['candidates']))
    result['first_failure_reasons'] = dict(Counter(row['failure']['reason'] for row in result['candidates'] if 'failure' in row))
    # Concretize only the unexpected-halting diagnostics, on a small valid
    # register frame.  Fuel/unsupported symbolic failures remain unresolved.
    literal_halts = []
    for row in result['candidates']:
        if row.get('failure', {}).get('reason') != 'unexpected_halt':
            continue
        index = row['failure']['index']
        pc, operation, register, branch, _ = cases[index]
        values = [0] * 10
        if branch is not None and not branch[1]:
            values[branch[0]] = 1
        initial = {-1, 40} | {i for i, bit in enumerate(pc) if bit == '1'}
        at = 41
        for value in values:
            at += 1
            initial.update(range(at, at + value + 1))
            at += value + 1
        if operation == 'CI' or (operation == 'CD' and branch is not None and not branch[1]):
            successor = proto['inc'](pc)
        elif operation == 'CD':
            successor = proto['inc'](proto['strip']('0', 1, pc))
        elif operation == 'CB':
            successor = proto['inc'](proto['strip']('0', register, pc))
        else:
            assert operation == 'CC'
            successor = proto['strip']('1', register, pc)
        target_values = list(values)
        if operation == 'CI':
            target_values[register] += 1
        elif operation == 'CD' and branch is not None and not branch[1]:
            target_values[register] -= 1
            target_values.append(0)
        expected_head = -int(successor is None)
        expected = {expected_head - 1, 40}
        expected.update(expected_head + i for i, bit in enumerate(successor or '') if bit == '1')
        at = 41
        for value in target_values:
            at += 1
            expected.update(range(at, at + value + 1))
            at += value + 1
        # Check the same concrete input against the unchanged variant as an
        # independent literal endpoint control, without invoking box summaries.
        bq, bhead, bones = '96', 0, set(initial)
        for baseline_steps in range(10001):
            if (baseline_steps > 0 and bq == '96' and bhead == expected_head
                    and bones == expected):
                break
            assert bq != halt and baseline_steps < 10000, \
                'Baseline did not reach the constructed prepared-frame endpoint'
            w, direction, bq = table[bq, int(bhead in bones)]
            if w:
                bones.add(bhead)
            else:
                bones.discard(bhead)
            bhead += 1 if direction == 'R' else -1
        candidate = fuse(table, row['deleted'], row['retained'], row['mask'])
        q, head, ones = '96', 0, set(initial)
        for steps in range(10001):
            if q == halt:
                break
            assert not (steps > 0 and q == '96' and head == expected_head and ones == expected), \
                'Concrete instruction already returned before the alleged unexpected halt'
            if steps == 10000:
                raise AssertionError('Unexpected-halt diagnostic did not concretize within10000 moves')
            w, direction, q = candidate[q, int(head in ones)]
            if w:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if direction == 'R' else -1
        assert operation != 'CH'
        literal_halts.append({'recipe': [row['deleted'], row['retained'], row['mask']],
            'case': index, 'path': pc, 'operation': operation, 'physical_registers': values,
            'initial': {'state': '96', 'head': 0, 'ones': sorted(initial)},
            'baseline_exact_endpoint_steps': baseline_steps,
            'halt': {'steps': steps, 'state': q, 'head': head, 'ones': sorted(ones)},
            'no_earlier_expected_instruction_endpoint': True,
            'scope': 'Literal finite halt from a valid prepared input; no blank-start claim.'})
    result['literal_prepared_halt_witnesses'] = literal_halts
    result['bounded_rejection_is_not_semantic_inequivalence'] = True
    save()
    print(json.dumps({key: result[key] for key in ('status', 'outcomes', 'first_failure_reasons',
                     'affine_survivors', 'boot_survivors', 'elapsed_seconds')}, indent=2), flush=True)
    print('Evidence:', output, flush=True)


if __name__ == '__main__':
    main()
