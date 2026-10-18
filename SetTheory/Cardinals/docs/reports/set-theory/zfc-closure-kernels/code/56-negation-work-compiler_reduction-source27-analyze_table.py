#!/usr/bin/env python3
"""Reproducible, purely syntactic audits of a binary TM transition table.

These audits do not establish blank-tape semantic reachability or minimality.
The bisimulation quotient keeps tape symbols and head moves fixed and only
identifies control states by deterministic Moore partition refinement.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError('Audit scripts require assertions; run without python -O.')


def parse_table(path):
    rows = {}
    start = None
    raw = Path(path).read_bytes()
    for line in raw.decode().splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, t = line.split()
            q, b, w, t = map(int, (q, b, w, t))
            assert (q, b) not in rows and b in (0, 1) and w in (0, 1) and d in ('L', 'R')
            rows[q, b] = (w, d, t)
    assert start is not None
    working = sorted({q for q, _ in rows})
    assert set(rows) == {(q, b) for q in working for b in (0, 1)}
    terminals = sorted({t for _, _, t in rows.values()} - set(working))
    return rows, start, working, terminals, hashlib.sha256(raw).hexdigest()


def audit(path):
    rows, start, working, terminals, sha = parse_table(path)
    reachable, todo = {start}, [start]
    while todo:
        q = todo.pop()
        for b in (0, 1):
            if (q, b) in rows:
                t = rows[q, b][2]
                if t not in reachable:
                    reachable.add(t)
                    todo.append(t)
    states = working + terminals
    part = {q: int(q not in working) for q in states}
    rounds = []
    while True:
        labels = {}
        refined = {}
        for q in states:
            sig = ('halt',) if q in terminals else tuple((w, d, part[t]) for w, d, t in (rows[q, 0], rows[q, 1]))
            if sig not in labels:
                labels[sig] = len(labels)
            refined[q] = labels[sig]
        rounds.append(len(labels))
        if all((part[q] == part[r]) == (refined[q] == refined[r]) for q in states for r in states):
            part = refined
            break
        part = refined
    groups = defaultdict(list)
    for q in working:
        groups[part[q]].append(q)
    exact = defaultdict(list)
    for q in working:
        exact[(rows[q, 0], rows[q, 1])].append(q)
    row_patterns = Counter(''.join(str(rows[q, b][0]) + rows[q, b][1] for b in (0, 1)) for q in working)
    pure_read = [q for q in working if rows[q, 0][:2] == (0, 'R') and rows[q, 1][:2] == (1, 'R')]
    return {
        'path': str(path), 'sha256': sha, 'start': start,
        'working_states': len(working), 'terminal_states': terminals, 'transitions': len(rows),
        'graph_reachable_working_states': len(set(working) & reachable),
        'graph_unreachable_working_states': sorted(set(working) - reachable),
        'exact_duplicate_state_groups': [v for v in exact.values() if len(v) > 1],
        'tape_preserving_bisimulation_round_class_counts_including_terminal': rounds,
        'bisimulation_quotient_working_states': len(groups),
        'nontrivial_bisimulation_classes': [v for v in groups.values() if len(v) > 1],
        'read_preserving_right_moving_states': len(pure_read),
        'row_output_patterns': dict(sorted(row_patterns.items())),
        'scope': 'Exact finite graph calculation; neither a semantic lower bound nor a search over different programs.'
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('tables', nargs='+', type=Path)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    out = json.dumps([audit(path) for path in a.tables], indent=2) + '\n'
    if a.output:
        a.output.write_text(out)
    print(out, end='')


if __name__ == '__main__':
    main()

