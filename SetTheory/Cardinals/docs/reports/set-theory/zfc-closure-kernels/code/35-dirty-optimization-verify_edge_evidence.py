#!/usr/bin/env python3
"""Independently replay every ledger witness of the incoming-edge search.

Imports only table parsing and abstract reachability from the search module;
does NOT call its trace, row checker, or certificate checker. Uses an ordinary
literal tape interpreter and direct set intersection for the bounded match.
"""
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
sys.dont_write_bytecode = True
import edge_replacement_search as core


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('machine', type=Path)
    ap.add_argument('report', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    assert __debug__
    start = time.monotonic()
    raw = a.machine.read_bytes()
    m = core.parse_table(raw.decode())
    report = json.loads(a.report.read_text())
    assert hashlib.sha256(raw).hexdigest() == report['machine_sha256']
    radius, bound = report['radius'], report['max_steps_per_side']
    windows = {q: set(xs) for q, xs in core.abstract_windows(m, radius).items()}
    rows_by_target = {p: {(q, b) for (q, b), e in m.rows.items()
                          if q != p and e.target == p} for p in m.states}

    def literal(q, bits, count, *, replacement=None, deleted=None, blocked=frozenset()):
        h = 0
        ones = {i - radius for i in range(2 * radius + 1) if bits & (1 << i)}
        out = []
        for step in range(count):
            if q == m.halt or not -radius <= h <= radius or q == deleted:
                break
            read = int(h in ones)
            if step and (q, read) in blocked:
                break
            edge = replacement if step == 0 and replacement is not None else m.rows[q, read]
            if edge.write:
                ones.add(h)
            else:
                ones.discard(h)
            h += edge.move
            q = edge.target
            if q != deleted:
                out.append(('halt',) if q == m.halt else (q, h, frozenset(ones)))
        return out

    @lru_cache(maxsize=8192)
    def originals(q, bits):
        return literal(q, bits, bound)

    seen, counts = defaultdict(set), Counter()
    digest = hashlib.sha256()
    with gzip.open(a.report.with_suffix('.ledger.jsonl.gz'), 'rb') as src:
        for line in src:
            digest.update(line)
            item = json.loads(line)
            kind, p, q, b, w, d, target, *evidence = item
            assert p != m.start and (q, b) in rows_by_target[p]
            assert target in m.states + [m.halt] and target != p
            assert w in (0, 1) and d in (-1, 1)
            group, choice = (p, q, b), (w, d, target)
            assert choice not in seen[group]
            seen[group].add(choice)
            edge = core.Edge(w, d, target)
            blocked = rows_by_target[p]
            if kind == 'fail':
                bits = evidence[0]
                assert bits in windows[q] and (bits >> radius) & 1 == b
                old = set(originals(q, bits))
                new = literal(q, bits, bound, replacement=edge, deleted=p, blocked=blocked)
                assert not old.intersection(new), ('false rejection', item)
                counts['negative_witnesses_replayed'] += 1
            else:
                assert kind == 'pass'
                cert = evidence[0]
                required = sorted(x for x in windows[q] if (x >> radius) & 1 == b)
                assert [c[0] for c in cert] == required
                for bits, n, k in cert:
                    assert 1 <= n <= bound and 1 <= k <= bound
                    old = literal(q, bits, n)
                    new = literal(q, bits, k, replacement=edge, deleted=p, blocked=blocked)
                    assert len(old) == n and len(new) == k and old[-1] == new[-1]
                    counts['positive_window_witnesses_replayed'] += 1
                counts['positive_transition_alternatives_replayed'] += 1
    assert digest.hexdigest() == report['ledger_uncompressed_sha256']
    expected = {(w, d, t) for w in (0, 1) for d in (-1, 1) for t in m.states + [m.halt]}
    for (p, q, b), choices in seen.items():
        assert choices == {x for x in expected if x[2] != p}
    assert len(seen) == report['source_rows_tested']
    assert sum(map(len, seen.values())) == report['transition_alternatives_tested']
    assert {d['removed'] for d in report['deletions']} == set(m.states) - {m.start}
    for deletion in report['deletions']:
        assert not deletion['accepted']
        assert deletion['tested_rows'][-1]['passing'] == 0
        for row in deletion['tested_rows']:
            assert (deletion['removed'], *row['row']) in seen
    out = {'all_checks_passed': True, **counts,
           'complete_alternative_sets_verified': len(seen),
           'nonstart_deletion_obstructions_verified': len(report['deletions']),
           'radius': radius, 'max_steps_per_side': bound,
           'elapsed_seconds': time.monotonic() - start,
           'machine_sha256': hashlib.sha256(raw).hexdigest(),
           'search_report_sha256': hashlib.sha256(a.report.read_bytes()).hexdigest(),
           'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'scope': 'Independent literal replay of finite local certificates, not a proof-assistant verification or a semantic lower bound.'}
    a.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
