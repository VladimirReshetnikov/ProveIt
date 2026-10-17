#!/usr/bin/env python3
"""Search independently synthesized incoming edges for deletion of a TM state.

This is a sufficient-certificate search, not a semantic decision procedure.
Each changed incoming row may change its write, direction, and destination.
For every original abstractly reachable local window, its replacement must
reach exactly an original positive-time configuration. The replacement block
may not execute any other changed row, nor enter the deleted state. Thus the
row certificates compose without selecting mutually dependent implementations.

The abstract reachability definition follows ProveIt's audit_tm.py: discard
one edge cell on every movement and admit both values at the newly exposed
edge. This overapproximates all blank-run windows. No code is imported from
the source repository and no input file is modified.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import time


@dataclass(frozen=True)
class Edge:
    write: int
    move: int
    target: int


@dataclass
class Machine:
    start: int
    halt: int
    rows: dict[tuple[int, int], Edge]

    @property
    def states(self):
        return sorted({q for q, _ in self.rows})


def parse_table(text):
    rows, start = {}, None
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith('#!'):
            m = re.fullmatch(r'#!\s+start\s+(\d+)', line)
            if not m or start is not None:
                raise ValueError('invalid/duplicate start')
            start = int(m[1])
        elif line and not line.startswith('#'):
            m = re.fullmatch(r'(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)', line)
            if not m:
                raise ValueError('invalid row')
            q, b, w, d, z = m.groups()
            key = int(q), int(b)
            if key in rows:
                raise ValueError('duplicate row')
            rows[key] = Edge(int(w), 1 if d == 'R' else -1, int(z))
    states = {q for q, _ in rows}
    if start not in states or set(rows) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError('invalid state domain')
    terminals = {e.target for e in rows.values()} - states
    if len(terminals) != 1:
        raise ValueError('ambiguous terminal')
    return Machine(start, terminals.pop(), rows)


def abstract_windows(machine, radius):
    width = 2 * radius + 1
    mask = (1 << width) - 1
    seen = {(machine.start, 0)}
    pending = deque(seen)
    out = defaultdict(list)
    while pending:
        q, bits = pending.popleft()
        out[q].append(bits)
        if q == machine.halt:
            continue
        e = machine.rows[q, (bits >> radius) & 1]
        bits = (bits & ~(1 << radius)) | (e.write << radius)
        if e.move == 1:
            bits, newbit = bits >> 1, 1 << (width - 1)
        else:
            bits, newbit = (bits << 1) & mask, 1
        for shifted in (bits, bits | newbit):
            item = (e.target, shifted)
            if item not in seen:
                seen.add(item)
                pending.append(item)
    return {q: sorted(xs) for q, xs in out.items()}


def trace(machine, q, bits, radius, bound, *, first=None, removed=None, blocked=frozenset()):
    """Full local configs after positive steps, including a final blocked config.

    Reading outside the initial window is forbidden. A final head may be just
    outside it: a match there still ensures whole-tape equality because neither
    run has written outside. Terminal configurations match on halting alone.
    """
    head, result, seen = 0, [], set()
    for step in range(bound):
        if q == machine.halt:
            return result, 'halt'
        if not -radius <= head <= radius:
            return result, 'window'
        if q == removed:
            return result, 'removed'
        b = (bits >> (head + radius)) & 1
        if (q, b) in blocked and not (step == 0 and first is not None):
            return result, 'changed_row'
        conf = q, head, bits
        if conf in seen:
            return result, 'cycle'
        seen.add(conf)
        e = first if step == 0 and first is not None else machine.rows[q, b]
        pos = head + radius
        bits = (bits & ~(1 << pos)) | (e.write << pos)
        head += e.move
        q = e.target
        result.append((q, head, bits))
    return result, 'fuel'


def key(machine, conf):
    return ('halt',) if conf[0] == machine.halt else conf


def check_row(machine, row, replacement, patterns, radius, bound, removed,
              changed_rows, originals):
    cert = []
    for bits in patterns:
        targets, old_length, old_end = originals[bits]
        new, new_end = trace(machine, row[0], bits, radius, bound,
                             first=replacement, removed=removed, blocked=changed_rows)
        for j, conf in enumerate(new, 1):
            k = key(machine, conf)
            if k in targets and conf[0] != removed:
                cert.append([bits, targets[k], j])
                break
        else:
            return None, [bits, old_length, old_end, len(new), new_end]
    return cert, None


def independent_check(machine, removed, replacements, windows, radius, bound, certificates):
    """Replay a positive certificate without the search's cached trace/index.

    Every reported step count is followed literally. The candidate's internal
    steps use only unmodified rows; matching is checked on exact local tapes.
    """
    changed = set(replacements)
    assert all(e.target != removed for row, e in machine.rows.items()
               if row[0] != removed and row not in changed)
    assert all(row[0] != removed and e.target != removed
               for row, e in replacements.items())
    for row, e in replacements.items():
        required = [x for x in windows[row[0]] if (x >> radius) & 1 == row[1]]
        cert = certificates[row]
        assert [x[0] for x in cert] == required
        for bits, n, m in cert:
            assert 1 <= n <= bound and 1 <= m <= bound
            def run(count, patched):
                q, h, tape = row[0], 0, bits
                for i in range(count):
                    assert q != machine.halt and -radius <= h <= radius
                    read = (tape >> (h + radius)) & 1
                    r = q, read
                    if patched:
                        assert q != removed
                        assert i == 0 or r not in changed
                    edge = e if patched and i == 0 else machine.rows[r]
                    p = h + radius
                    tape = (tape & ~(1 << p)) | (edge.write << p)
                    h += edge.move
                    q = edge.target
                return q, h, tape
            a, b = run(n, False), run(m, True)
            assert b[0] != removed
            assert (a[0] == b[0] == machine.halt) or a == b
    return True


def run_search(machine, radius, bound, ledger_path):
    start = time.monotonic()
    windows = abstract_windows(machine, radius)
    setup_time = time.monotonic() - start
    states = machine.states
    # A start-state deletion also needs a new blank-start certificate. This
    # experiment deliberately covers every NONSTART deletion, with unchanged
    # initial configuration, so no undocumented initial tape is smuggled in.
    summaries, candidates, total, row_count = [], [], 0, 0
    digest = hashlib.sha256()
    with open(ledger_path, 'wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as gz:
        def record(obj):
            line = (json.dumps(obj, separators=(',', ':')) + '\n').encode()
            gz.write(line)
            digest.update(line)
        for removed in states:
            if removed == machine.start:
                continue
            incoming = sorted([row for row, e in machine.rows.items()
                               if row[0] != removed and e.target == removed])
            patterns_for = {row: [p for p in windows.get(row[0], [])
                                  if (p >> radius) & 1 == row[1]] for row in incoming}
            incoming.sort(key=lambda row: (len(patterns_for[row]), row))
            changed = frozenset(incoming)
            selected, certs, row_summaries = {}, {}, []
            for row in incoming:
                row_count += 1
                patterns = patterns_for[row]
                originals = {}
                for bits in patterns:
                    old, reason = trace(machine, row[0], bits, radius, bound)
                    index = {}
                    for i, c in enumerate(old, 1):
                        if c[0] != removed:
                            index.setdefault(key(machine, c), i)
                    originals[bits] = index, len(old), reason
                options, failures = [], Counter()
                # Preserve familiar choices first, but exhaust all 4*n legal
                # triples (write, movement, remaining working/terminal target).
                old = machine.rows[row]
                targets = [q for q in states + [machine.halt] if q != removed]
                triples = sorted((Edge(w, d, q) for w in (0, 1) for d in (-1, 1) for q in targets),
                                 key=lambda e: (e.write != old.write, e.move != old.move, e.target))
                for edge in triples:
                    total += 1
                    cert, fail = check_row(machine, row, edge, patterns, radius, bound,
                                           removed, changed, originals)
                    if cert is not None:
                        options.append((edge, cert))
                        record(['pass', removed, *row, edge.write, edge.move, edge.target, cert])
                    else:
                        failures[fail[-1]] += 1
                        record(['fail', removed, *row, edge.write, edge.move, edge.target, *fail])
                row_summaries.append({'row': list(row), 'windows': len(patterns),
                                      'alternatives': len(triples), 'passing': len(options),
                                      'candidate_stop_reasons': dict(failures),
                                      'passing_edges': [[e.write, e.move, e.target] for e, _ in options]})
                if not options:
                    break
                selected[row], certs[row] = options[0]
            passed = len(selected) == len(incoming)
            if passed:
                independent_check(machine, removed, selected, windows, radius, bound, certs)
                candidates.append({'removed': removed,
                                   'replacements': [[*row, e.write, e.move, e.target]
                                                    for row, e in selected.items()],
                                   'certificates': [[*row, c] for row, c in certs.items()]})
            summaries.append({'removed': removed, 'incoming_rows': [list(r) for r in incoming],
                              'tested_rows': row_summaries, 'accepted': passed})
            if removed % 25 == 0:
                print(f'state {removed}: {total} transition alternatives, {len(candidates)} candidates', flush=True)
    return {'schema': 1, 'family': 'independent incoming write/direction/target synthesis',
            'states': len(states), 'start': machine.start, 'halt': machine.halt,
            'radius': radius, 'max_steps_per_side': bound,
            'abstract_configurations': sum(map(len, windows.values())),
            'states_present': len(windows),
            'abstractly_possible_rows': len({(q, (p >> radius) & 1)
                for q, xs in windows.items() if q != machine.halt for p in xs}),
            'nonstart_deletions_tested': len(summaries), 'source_rows_tested': row_count,
            'transition_alternatives_tested': total, 'setup_seconds': setup_time,
            'total_seconds': time.monotonic() - start, 'candidates': candidates,
            'ledger_uncompressed_sha256': digest.hexdigest(), 'deletions': summaries,
            'scope': 'No accepted candidate means no certificate in this bounded family; it is not a lower bound or a proof that any rejected machine is semantically wrong.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('machine', type=Path)
    parser.add_argument('--radius', type=int, default=6)
    parser.add_argument('--steps', type=int, default=128)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert __debug__, 'run without -O'
    assert 1 <= args.radius <= 10 and args.steps > 0
    data = args.machine.read_bytes()
    machine = parse_table(data.decode())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    result = run_search(machine, args.radius, args.steps, args.output.with_suffix('.ledger.jsonl.gz'))
    result.update(machine_sha256=hashlib.sha256(data).hexdigest(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'deletions'}, indent=2))


if __name__ == '__main__':
    main()
