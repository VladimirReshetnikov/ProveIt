#!/usr/bin/env python3
"""Exact rooted deterministic labelled-graph comparisons of literal TM files."""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path


def parse(path):
    table = {}
    start = 0
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        fields = line.split()
        if not fields or fields[0].startswith('#'):
            continue
        if len(fields) != 5 or fields[3] not in ('L', 'R'):
            raise ValueError('Unsupported literal format')
        q, b, w, d, z = fields
        q, b, w, z = map(int, (q, b, w, z))
        if b not in (0, 1) or w not in (0, 1) or (q, b) in table:
            raise ValueError('Not a deterministic binary table')
        table[q, b] = (w, -1 if d == 'L' else 1, z)
    states = {q for q, b in table}
    if len(table) != 2 * len(states):
        raise ValueError('Incomplete working state')
    if start not in states:
        raise ValueError('Missing start')
    return start, table


def rooted(a, b, reflect=False):
    s, ta = a
    t, tb = b
    todo = deque([(s, t)])
    forward, backward = {s: t}, {t: s}
    while todo:
        q, r = todo.popleft()
        for bit in (0, 1):
            x, y = ta.get((q, bit)), tb.get((r, bit))
            if (x is None) != (y is None):
                return {'equal': False, 'reason': 'halt/working mismatch', 'states': [q, r], 'read': bit}
            if x is None:
                continue
            w, d, z = x
            v, e, u = y
            if reflect:
                e = -e
            if (w, d) != (v, e):
                return {'equal': False, 'reason': 'action mismatch', 'states': [q, r], 'read': bit, 'actions': [[w, d], [v, e]]}
            if (z in forward and forward[z] != u) or (u in backward and backward[u] != z):
                return {'equal': False, 'reason': 'inconsistent bijection', 'states': [q, r], 'read': bit, 'targets': [z, u]}
            if z not in forward:
                forward[z] = u
                backward[u] = z
                todo.append((z, u))
    return {'equal': True, 'reached_states_including_halt': len(forward), 'mapping': forward}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--candidate', type=Path, required=True)
    p.add_argument('--roots', type=Path, nargs='+', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    cand = parse(a.candidate)
    items, failed, seen = [], [], set()
    for root in a.roots:
        for path in sorted(root.rglob('*.tm')):
            raw = path.read_bytes()
            digest = hashlib.sha256(raw).hexdigest()
            if digest in seen:
                continue
            try:
                base = parse(path)
            except (ValueError, UnicodeError) as exc:
                failed.append({'path': str(path), 'reason': str(exc)})
                continue
            seen.add(digest)
            if len(base[1]) != len(cand[1]):
                continue
            items.append({'path': str(path), 'sha256': digest,
                          'states': len(base[1]) // 2,
                          'rooted': rooted(cand, base),
                          'reflected': rooted(cand, base, True)})
    result = {'candidate': str(a.candidate),
              'candidate_sha256': hashlib.sha256(a.candidate.read_bytes()).hexdigest(),
              'distinct_same_size_literal_tables': len(items),
              'identical_rooted': [x['path'] for x in items if x['rooted']['equal']],
              'identical_reflected': [x['path'] for x in items if x['reflected']['equal']],
              'comparisons': items, 'unsupported_files': failed}
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('comparisons', 'unsupported_files')}, indent=2))


if __name__ == '__main__':
    main()
