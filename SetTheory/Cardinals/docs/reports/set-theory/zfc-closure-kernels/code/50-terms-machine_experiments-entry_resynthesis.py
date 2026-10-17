#!/usr/bin/env python3
"""Resynthesize every incoming action while deleting one permutation252 state.

This is a bounded executable diagnostic, not a machine-equivalence proof.
The finite family includes write, direction, and target changes, including
halting targets. Joint changes are chosen lazily; there is no independent
one-row screening restriction. Full affine checks and a whole-tape blank
bootstrap are required before a candidate is reported as a survivor.

The strict affine executor and box contracts are attributed to the pinned
ProveIt/Mira-Cult/Jeff/Wade sources. Only 55 supporting box rows are protected.
No baseline file is modified. All unfinished assignments are explicitly saved.
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
import time
from types import SimpleNamespace

sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class NeedAction(Exception):
    def __init__(self, index):
        self.index = index


class PartialTable(dict):
    def __init__(self, rows, pending=None):
        super().__init__(rows)
        self.pending = pending or {}
        self.used = set()

    def __getitem__(self, row):
        self.used.add(row)
        if row in self.pending:
            raise NeedAction(self.pending[row])
        return super().__getitem__(row)


class Harness:
    def __init__(self, repo, fuel):
        self.repo = repo
        self.base = repo / 'Computability/BusyBeaver/Research/ZFC'
        audit_file = self.base / 'candidate252_independent_audit.py'
        self.audit = load('entry_resynthesis_audit', audit_file)
        self.source = self.base / 'candidate-permutation252/zfc_permutation252_old.tm'
        data = self.source.read_bytes()
        self.numeric = self.audit.read_table(data)
        canonical = self.audit.encode(self.numeric)
        assert data.rstrip() + b'\n' == canonical
        assert hashlib.sha256(canonical).hexdigest() == self.audit.EXPECTED_SHA
        self.table = {(str(q), b): (w, d, str(t))
                      for (q, b), (w, d, t) in self.numeric.items()}
        self.states = sorted({q for q, b in self.table}, key=int)
        self.protected = {(str(q), b) for q, b in self.audit.BOX_PAIRS}
        assert len(self.states) == 252 and len(self.table) == 504
        assert len(self.protected) == 55
        strict_file = repo / ('SetTheory/Cardinals/docs/reports/set-theory/'
                              'zfc-closure-kernels/code/'
                              '27-variant-experiments-machine_search-grammar_search-strict_affine.py')
        sys.modules['cost_search'] = SimpleNamespace()
        self.strict = load('entry_resynthesis_strict', strict_file)
        program_file = repo / 'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
        text = program_file.read_text().split('Definition p254_tab', 1)[1]
        text = text.split('[', 1)[1].split('].', 1)[0]
        edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
        nodes = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', text)
        assert len(nodes) == 6459
        self.cases = []

        def visit(node, prefix):
            for b, instruction in enumerate(nodes[node]):
                path = prefix + str(b)
                op, *args = instruction.split()
                if op == 'CN':
                    visit(int(args[0]), path)
                    continue
                r = int(args[0]) if args else None
                for zero in ((True, False) if op == 'CD' else (None,)):
                    p = self.audit.NEWPHYS[r] if op in ('CI', 'CD') else r
                    branch = (p, zero) if op == 'CD' else None
                    successor = self.audit.successor(path, op, r, zero)
                    effect = ('inc', p) if op == 'CI' else (
                        ('dec', p) if op == 'CD' and not zero else None)
                    right = [('b', int(c)) for c in successor] if successor is not None else []
                    right += [('r', 0, 1, (41 if successor is None else 40)
                               - len(successor or '')),
                              ('b', 1), ('box', ('plain', effect))]
                    self.cases.append((path, op, r, zero, branch,
                                       self.strict.canon([('b', 1)], right)))

        visit(0, '')
        assert len(self.cases) == 8391
        self.fuel = fuel
        self.usage = defaultdict(set)
        self.cost = {}
        for index in range(len(self.cases)):
            traced = PartialTable(self.table)
            ok, cost, reason = self.check(traced, index)
            assert ok, ('baseline', index, reason)
            self.cost[index] = cost
            for row in traced.used:
                self.usage[row].add(index)
        spares = [0] * 65
        spares[8] = 1
        self.target_ones = self.audit.paint('', 40, [0] * 9, spares, 2)
        q, h, ones, _, _ = self.audit.run_prefix(self.numeric, 82552)
        assert (q, h, ones) == (96, 2, self.target_ones)
        self.hashes = {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in (self.source, audit_file, strict_file, program_file)}

    def check(self, table, index):
        path, op, _, _, branch, target = self.cases[index]
        try:
            rules, literals = self.strict.run(table, path, branch, target,
                                              halt=op == 'CH', fuel=self.fuel)
            assert literals > 0
            return True, sum(rules.values()), None
        except AssertionError as error:
            return False, 0, ('fuel' if str(error) == 'symbolic fuel exhausted'
                              else 'unsupported_symbolic_rule')
        except KeyError:
            return False, 0, 'missing_transition'

    def blank(self, table, limit):
        state, head, ones = '64', 0, set()
        for tick in range(limit + 1):
            if (state, head, ones) == ('96', 2, self.target_ones):
                return {'outcome': 'exact_frozen_whole_frame', 'steps': tick}
            if state == '254':
                return {'outcome': 'halt', 'steps': tick}
            if tick == limit:
                return {'outcome': 'fuel_limit', 'steps': tick}
            w, direction, state = table[state, int(head in ones)]
            if w:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if direction == 'R' else -1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--degree', type=int, choices=(1, 2), required=True)
    parser.add_argument('--seconds', type=float, default=600)
    parser.add_argument('--affine-fuel', type=int, default=1000)
    parser.add_argument('--boot-limit', type=int, default=1000000)
    parser.add_argument('--state', type=int, help='Restrict to one eligible deleted state.')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must remain enabled')
    repo, output = args.repo.resolve(), args.output.resolve()
    if output == repo or repo in output.parents:
        parser.error('Output must be outside the baseline repository')
    output.parent.mkdir(parents=True, exist_ok=True)
    begun = time.monotonic()
    h = Harness(repo, args.affine_fuel)
    protected_targets = {h.table[k][2] for k in h.protected}
    eligible = [q for q in h.states if q not in {'64', '96'}
                and q not in protected_targets
                and all((q, b) not in h.protected for b in (0, 1))]
    incoming = {q: sorted((k for k, v in h.table.items()
                           if v[2] == q and k[0] != q),
                          key=lambda k: (int(k[0]), k[1])) for q in eligible}
    family = [q for q in eligible if len(incoming[q]) == args.degree]
    assert len(family) == (131 if args.degree == 1 else 46)
    if args.state is not None:
        family = [q for q in family if q == str(args.state)]
        if not family:
            parser.error('Requested state is not eligible at the selected degree')
    assert all(h.usage[k] for q in family for k in incoming[q])
    # Favor the known exact-PC obstruction, then the historically distinct
    # zero/positive contexts; this changes only traversal order.
    family.sort(key=lambda q: (q not in {'204', '107'}, int(q)))
    affected = {q: sorted(set.union(*(h.usage[k] for k in incoming[q])),
                          key=lambda i: (h.cost[i], i)) for q in family}
    domains = {q: list(itertools.product((0, 1), ('L', 'R'),
                                         [t for t in h.states + ['254'] if t != q]))
               for q in family}
    assert all(len(domain) == 1008 for domain in domains.values())
    groups = {q: {'deleted_state': int(q), 'incoming_rows': [list(k) for k in incoming[q]],
                  'planned': 1008 ** args.degree, 'pruned': 0,
                  'nodes': 0, 'survivors': 0} for q in family}
    stack = [(q, {}) for q in reversed(family)]
    record = {'status': 'running', 'scope': __doc__,
              'source_commit': 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
              'inputs_sha256': h.hashes,
              'driver_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'baseline_affine_cases': 8391, 'baseline_exact_blank_steps': 82552,
              'logical_to_physical': list(h.audit.NEWPHYS),
              'working_states_after_deletion': 251, 'row_count_after_deletion': 502,
              'protected_box_rows': 55, 'start_state': 64, 'halt_state': 254,
              'domain_size_per_incoming_row': 1008,
              'domain_definition': 'Two writes times two directions times 251 surviving working states plus halt.',
              'joint_compensation_allowed': True,
              'degree': args.degree, 'planned': len(family) * 1008 ** args.degree,
              'nodes': 0, 'affine_checks': 0, 'full_recheck_cases': 0,
              'pruned': 0, 'survivors': [], 'blank_survivors': [],
              'groups': list(groups.values()), 'failures': {},
              'affine_fuel': args.affine_fuel, 'seconds_limit': args.seconds,
              'boot_limit': args.boot_limit, 'command': [sys.executable, *sys.argv],
              'python': platform.python_version()}
    failures = Counter()
    weight = lambda assignment: 1008 ** (args.degree - len(assignment))

    def save():
        record['elapsed_seconds'] = time.monotonic() - begun
        record['failures'] = dict(failures)
        record['frontier'] = [{'deleted_state': int(q),
                               'assigned_actions': {str(i): list(v) for i, v in a.items()},
                               'completions': weight(a)} for q, a in reversed(stack)]
        record['remaining'] = sum(weight(a) for _, a in stack)
        assert record['planned'] == record['pruned'] + len(record['survivors']) + record['remaining']
        output.write_text(json.dumps(record, indent=2) + '\n')

    journal_path = output.with_suffix('.jsonl')
    save()
    print(json.dumps({'baseline': 'PASS', 'planned': record['planned'],
                      'degree': args.degree}), flush=True)
    with journal_path.open('w') as journal:
        while stack and time.monotonic() - begun < args.seconds:
            dead, assigned = stack.pop()
            group = groups[dead]
            rows = incoming[dead]
            current = {k: v for k, v in h.table.items() if k[0] != dead}
            for i, action in assigned.items():
                current[rows[i]] = action
            pending = {rows[i]: i for i in range(args.degree) if i not in assigned}
            current = PartialTable(current, pending)
            assert all(current[k] == h.table[k] for k in h.protected)
            fail_index = reason = needed = None
            try:
                for index in affected[dead]:
                    ok, _, reason = h.check(current, index)
                    record['affine_checks'] += 1
                    if not ok:
                        fail_index = index
                        break
                if fail_index is None:
                    for index in range(len(h.cases)):
                        ok, _, reason = h.check(current, index)
                        record['full_recheck_cases'] += 1
                        if not ok:
                            fail_index = index
                            break
            except NeedAction as request:
                needed = request.index
            group['nodes'] += 1
            record['nodes'] += 1
            entry = {'deleted_state': int(dead),
                     'assigned_actions': {str(i): list(v) for i, v in assigned.items()}}
            if needed is not None:
                assert needed not in assigned
                entry.update(outcome='branch', incoming_index=needed)
                for action in reversed(domains[dead]):
                    stack.append((dead, {**assigned, needed: action}))
            elif fail_index is not None:
                amount = weight(assigned)
                record['pruned'] += amount
                group['pruned'] += amount
                failures[reason] += 1
                entry.update(outcome='prune', first_failure_case=fail_index,
                             reason=reason, completions=amount)
            elif len(assigned) < args.degree:
                needed = next(i for i in range(args.degree) if i not in assigned)
                entry.update(outcome='branch_unused', incoming_index=needed)
                for action in reversed(domains[dead]):
                    stack.append((dead, {**assigned, needed: action}))
            else:
                assert len(current) == 502
                assert all(t != dead for _, _, t in current.values())
                encoded = ('#! start 64\n' + ''.join(
                    f'{q} {b} {w} {d} {t}\n' for (q, b), (w, d, t)
                    in sorted(current.items(), key=lambda row: (int(row[0][0]), row[0][1])))).encode()
                candidate_file = output.parent / f'entry_candidate_{dead}_{record["nodes"]}.tm'
                candidate_file.write_bytes(encoded)
                entry.update(outcome='affine_survivor', table=str(candidate_file),
                             table_sha256=hashlib.sha256(encoded).hexdigest(),
                             blank=h.blank(current, args.boot_limit))
                record['survivors'].append(entry)
                group['survivors'] += 1
                if entry['blank']['outcome'] == 'exact_frozen_whole_frame':
                    record['blank_survivors'].append(entry)
                print(json.dumps(entry), flush=True)
            journal.write(json.dumps(entry, separators=(',', ':')) + '\n')
            if record['nodes'] % 2000 == 0:
                journal.flush()
                save()
            if not stack or stack[-1][0] != dead:
                print(json.dumps({'state_finished': int(dead), 'group': group}), flush=True)
    record['status'] = 'completed' if not stack else 'time_bound_partial'
    record['journal'] = {'file': journal_path.name,
                         'bytes': journal_path.stat().st_size,
                         'sha256': hashlib.sha256(journal_path.read_bytes()).hexdigest()}
    save()
    print(json.dumps({k: record[k] for k in ('status', 'planned', 'pruned', 'remaining',
                                           'nodes', 'affine_checks', 'elapsed_seconds')}), flush=True)


if __name__ == '__main__':
    main()
