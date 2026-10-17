#!/usr/bin/env python3
"""Use certified partial redirections to refine an incoming-edge deletion.

At the first stage, each supplied rewrite has an independently replayed local
certificate in the original machine. Its internal steps execute no other
rewritten incoming row. At the second stage, the abstract reachable windows
are recomputed for that altered 253-state machine, then the remaining incoming
rows of the same proposed deleted state are synthesized. These are equivalent
machines before deletion; no finite simulation is treated as a proof.
"""
import argparse
from collections import Counter
import gzip
import hashlib
from itertools import product
import json
from pathlib import Path
import time
import sys
sys.dont_write_bytecode = True
import edge_replacement_search as core


def verify_partial(machine, removed, replacements, certificates, windows, radius, bound):
    changed = set(replacements)
    for row, e in replacements.items():
        required = [x for x in windows[row[0]] if (x >> radius) & 1 == row[1]]
        assert [c[0] for c in certificates[row]] == required
        for bits, old_steps, new_steps in certificates[row]:
            def run(count, candidate):
                assert 1 <= count <= bound
                q, head, tape = row[0], 0, bits
                for step in range(count):
                    assert q != machine.halt and -radius <= head <= radius
                    read = (tape >> (head + radius)) & 1
                    pair = q, read
                    if candidate:
                        assert q != removed
                        assert step == 0 or pair not in changed
                    edge = replacements[pair] if candidate and step == 0 else machine.rows[pair]
                    pos = head + radius
                    tape = (tape & ~(1 << pos)) | (edge.write << pos)
                    q, head = edge.target, head + edge.move
                return q, head, tape
            a, b = run(old_steps, False), run(new_steps, True)
            assert b[0] != removed
            assert (a[0] == b[0] == machine.halt) or a == b


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('machine', type=Path)
    parser.add_argument('seed_report', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert __debug__
    start = time.monotonic()
    raw = args.machine.read_bytes()
    machine = core.parse_table(raw.decode())
    seed = json.loads(args.seed_report.read_text())
    assert hashlib.sha256(raw).hexdigest() == seed['machine_sha256']
    radius, bound = seed['radius'], seed['max_steps_per_side']
    old_windows = core.abstract_windows(machine, radius)
    by_removed = {}
    with gzip.open(args.seed_report.with_suffix('.ledger.jsonl.gz'), 'rt') as src:
        for line in src:
            item = json.loads(line)
            if item[0] == 'pass':
                _, removed, q, b, w, d, target, cert = item
                by_removed.setdefault(removed, {}).setdefault((q, b), []).append((core.Edge(w, d, target), cert))
    report, accepted, alternative_count = [], [], 0
    ledger = args.output.with_suffix('.ledger.jsonl.gz')
    digest = hashlib.sha256()
    with open(ledger, 'wb') as rawlog, gzip.GzipFile(fileobj=rawlog, mode='wb', mtime=0) as log:
        def record(item):
            line = (json.dumps(item, separators=(',', ':')) + '\n').encode()
            log.write(line)
            digest.update(line)
        for removed, choices in sorted(by_removed.items()):
            rows = sorted(choices)
            for variant, chosen in enumerate(product(*(choices[r] for r in rows))):
                replacements = {r: e for r, (e, _) in zip(rows, chosen)}
                certs = {r: c for r, (_, c) in zip(rows, chosen)}
                verify_partial(machine, removed, replacements, certs, old_windows, radius, bound)
                table = dict(machine.rows)
                table.update(replacements)
                modified = core.Machine(machine.start, machine.halt, table)
                windows = core.abstract_windows(modified, radius)
                incoming = [r for r, e in table.items() if r[0] != removed and e.target == removed]
                pat = {r: [x for x in windows[r[0]] if (x >> radius) & 1 == r[1]] for r in incoming}
                incoming.sort(key=lambda r: (len(pat[r]), r))
                blocked = frozenset(incoming)
                selected, selected_certs, row_reports = {}, {}, []
                for row in incoming:
                    originals = {}
                    for bits in pat[row]:
                        trace, stop = core.trace(modified, row[0], bits, radius, bound)
                        targets = {}
                        for i, conf in enumerate(trace, 1):
                            if conf[0] != removed:
                                targets.setdefault(core.key(modified, conf), i)
                        originals[bits] = targets, len(trace), stop
                    failures, options = Counter(), []
                    for w, d, target in product((0, 1), (-1, 1), modified.states + [modified.halt]):
                        if target == removed:
                            continue
                        alternative_count += 1
                        edge = core.Edge(w, d, target)
                        cert, failure = core.check_row(modified, row, edge, pat[row], radius, bound,
                                                       removed, blocked, originals)
                        if cert is not None:
                            options.append((edge, cert))
                            record(['pass', removed, variant, *row, w, d, target, cert])
                        else:
                            failures[failure[-1]] += 1
                            record(['fail', removed, variant, *row, w, d, target, *failure])
                    row_reports.append({'row': list(row), 'windows': len(pat[row]),
                                        'passing_options': len(options), 'failures': dict(failures)})
                    if not options:
                        break
                    selected[row], selected_certs[row] = options[0]
                passed = len(selected) == len(incoming)
                obj = {'removed': removed, 'variant': variant,
                       'certified_seed_rewrites': [[*r, e.write, e.move, e.target] for r, e in replacements.items()],
                       'abstract_configurations': sum(map(len, windows.values())),
                       'remaining_incoming': [list(r) for r in incoming],
                       'row_reports': row_reports, 'accepted': passed}
                if passed:
                    core.independent_check(modified, removed, selected, windows, radius, bound, selected_certs)
                    obj['final_rewrites'] = [[*r, e.write, e.move, e.target] for r, e in selected.items()]
                    obj['final_certificates'] = [[*r, c] for r, c in selected_certs.items()]
                    accepted.append(obj)
                report.append(obj)
            print(f'removal {removed}: {len(report)} variants, {alternative_count} alternatives, {len(accepted)} accepted', flush=True)
    out = {'schema': 1, 'machine_sha256': hashlib.sha256(raw).hexdigest(),
           'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'core_sha256': hashlib.sha256(Path(core.__file__).read_bytes()).hexdigest(),
           'seed_report_sha256': hashlib.sha256(args.seed_report.read_bytes()).hexdigest(),
           'radius': radius, 'max_steps_per_side': bound,
           'certified_partial_rewrite_variants': len(report),
           'transition_alternatives_tested': alternative_count,
           'complete_deletion_candidates': accepted,
           'total_seconds': time.monotonic() - start,
           'ledger_uncompressed_sha256': digest.hexdigest(), 'variants': report,
           'scope': 'Bounded sufficient-certificate family only. No rejected candidate is proved semantically invalid.'}
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'variants'}, indent=2))


if __name__ == '__main__':
    main()
