#!/usr/bin/env python3
"""Rebuild the pinned literal-table census and compare proposed machines.

This is a finite graph audit, not an arithmetic correctness certificate.
All paths are recorded relative to the source checkout or incoming extraction.
"""
import argparse
import csv
import hashlib
import io
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
PIN = '603c58ca3bd6bf3222fcfc4e308e6b079f65d573'


def parse(data):
    rows = {}
    declared = None
    for line in data.decode('ascii').splitlines():
        if not line.strip():
            continue
        if line.lstrip().startswith('#'):
            m = re.search(r'\bstart\s*(\d+)', line)
            if m and declared is None:
                declared = int(m[1])
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        if (q, b) in rows or b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R'):
            raise ValueError('Invalid or repeated transition')
        rows[q, b] = (w, int(d == 'R'), n)
    states = {q for q, b in rows}
    if not states or len(rows) != 2 * len(states):
        raise ValueError('Incomplete table')
    if any((q, b) not in rows for q in states for b in (0, 1)):
        raise ValueError('Incomplete table')
    halt = {n for w, d, n in rows.values()} - states
    if len(halt) != 1:
        raise ValueError('Table does not have a unique terminal halt label')
    start = declared if declared is not None else (0 if states == set(range(len(states))) else None)
    return rows, states, start


def spanning_roots(rows, states):
    # Source SCC of the condensation, if unique. An iterative implementation
    # avoids Python recursion limits on larger historical tables.
    adj = {q: [rows[q, b][2] for b in (0, 1) if rows[q, b][2] in states] for q in states}
    rev = {q: [] for q in states}
    for q, ns in adj.items():
        for n in ns:
            rev[n].append(q)
    seen, order = set(), []
    for start in sorted(states):
        stack = [(start, False)]
        while stack:
            q, post = stack.pop()
            if post:
                order.append(q)
            elif q not in seen:
                seen.add(q)
                stack.append((q, True))
                stack.extend((n, False) for n in adj[q] if n not in seen)
    groups, comp = [], {}
    for start in reversed(order):
        if start in comp:
            continue
        k = len(groups)
        groups.append([])
        stack = [start]
        while stack:
            q = stack.pop()
            if q in comp:
                continue
            comp[q] = k
            groups[k].append(q)
            stack.extend(n for n in rev[q] if n not in comp)
    incoming = {comp[n] for q, ns in adj.items() for n in ns if comp[q] != comp[n]}
    sources = set(range(len(groups))) - incoming
    return sorted(groups[next(iter(sources))]) if len(sources) == 1 else []


def canonical(rows, states, strong=False):
    """Exact complete tuple, minimized over spanning roots and symmetries.

    Strong mode additionally allows reflection, bit exchange, and ignores
    final write/move. Bit exchange is a structural test, not a claimed
    semantic equivalence for a fixed zero-blank convention.
    """
    roots = spanning_roots(rows, states)
    best = None
    for flip in range(2 if strong else 1):
        for mirror in range(2 if strong else 1):
            for root in roots:
                index, order, out = {root: 0}, [root], []
                comparison = 0
                abandoned = False
                for q in order:
                    for b in (0, 1):
                        w, d, n = rows[q, b ^ flip]
                        if n in states:
                            if n not in index:
                                index[n] = len(order)
                                order.append(n)
                            triple = (w ^ flip, d ^ mirror, index[n])
                        else:
                            triple = (0, 0, -1) if strong else (w, d, -1)
                        for x in triple:
                            if best is not None and comparison == 0:
                                y = best[len(out)]
                                comparison = (x > y) - (x < y)
                                if comparison > 0:
                                    abandoned = True
                                    break
                            out.append(x)
                        if abandoned:
                            break
                    if abandoned:
                        break
                if not abandoned:
                    assert len(order) == len(states)
                    candidate = tuple(out)
                    if best is None or candidate < best:
                        best = candidate
    return best


def digest(data):
    return hashlib.sha256(data).hexdigest()


def tuple_digest(t):
    return digest(json.dumps(t, separators=(',', ':')).encode())


def quotient_count(rows, states):
    groups = {q: 0 for q in states}
    while True:
        bucket, updated = {}, {}
        for q in sorted(states):
            key = tuple((w, d, groups[n] if n in states else -1)
                        for w, d, n in (rows[q, 0], rows[q, 1]))
            updated[q] = bucket.setdefault(key, len(bucket))
        if len(set(updated.values())) == len(set(groups.values())):
            return len(bucket)
        groups = updated


def build(repo, incoming, out):
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    assert head == PIN, (head, PIN)
    paths = subprocess.check_output(['git', '-C', str(repo), 'ls-tree', '-r', '--name-only', PIN,
                                    'Computability/BusyBeaver/Research/PA'], text=True).splitlines()
    required = [p for p in paths if p.endswith('.tm')]
    missing = [p for p in required if not (repo / p).is_file()]
    assert not missing, missing
    occurrences = [(str(p.relative_to(repo)), p) for p in (repo / p for p in required)]
    occurrences += [('incoming/' + str(p.relative_to(incoming)), p)
                    for p in sorted(incoming.rglob('*.tm'))]
    cache, records, classes, rejects = {}, [], {}, []
    for location, path in occurrences:
        data = path.read_bytes()
        h = digest(data)
        if h not in cache:
            try:
                rows, states, start = parse(data)
                key = canonical(rows, states)
                info = dict(working_states=len(states), start=start,
                            spanning=key is not None, canonical_class=tuple_digest(key) if key else None)
                cache[h] = info
                if len(states) == 194 and key is not None and key not in classes:
                    strong = canonical(rows, states, True)
                    classes[key] = dict(canonical_class=tuple_digest(key), strong_class=tuple_digest(strong),
                                        sha256=h, representative=location, rows=rows, states=states,
                                        data=data, sources=[], quotient_states=quotient_count(rows, states))
            except Exception as exc:
                cache[h] = {'error': str(exc)}
        info = cache[h]
        rec = dict(path=location, sha256=h, bytes=len(data), **info)
        records.append(rec)
        if info.get('working_states') == 194 and info.get('spanning'):
            # Canonical-class digests only index data here; exact tuples above
            # establish equivalence and are compared again by the offline verifier.
            for c in classes.values():
                if c['canonical_class'] == info['canonical_class']:
                    c['sources'].append(location)
                    break
        if 'error' in info:
            rejects.append(rec)
    out.mkdir(parents=True, exist_ok=True)
    (out / 'frontier194').mkdir(exist_ok=True)
    ledger = []
    for c in sorted(classes.values(), key=lambda c: c['canonical_class']):
        target = Path('frontier194') / (c['canonical_class'][:16] + '.tm')
        (out / target).write_bytes(c['data'])
        ledger.append({k: v for k, v in c.items() if k not in ('rows', 'states', 'data')} | {'table_file': str(target)})
    by_state = Counter(r.get('working_states') for r in records if 'error' not in r)
    summary = dict(source_commit=PIN, tracked_pa_tm_files=len(required), incoming_tm_occurrences=len(occurrences)-len(required),
                   total_occurrences=len(records), unique_contents=len(cache), literal194_occurrences=by_state[194],
                   spanning194_classes=len(ledger), strong194_classes=len({c['strong_class'] for c in ledger}),
                   ordinary_nontrivial_quotients=[c['canonical_class'] for c in ledger if c['quotient_states'] < 194],
                   disconnected194_occurrences=sum(r.get('working_states') == 194 and not r.get('spanning') for r in records),
                   invalid_tables=rejects, occurrences_by_state=dict(sorted(by_state.items())),
                   scope='Every tracked literal .tm in the PA subtree and every .tm in the five current ZIPs, including their bundled reference tables. Historical explicit-JSON designs represented by these tables are included; arbitrary generators are not evaluated by this census.')
    (out / 'census.json').write_text(json.dumps(records, indent=2) + '\n')
    (out / 'frontier194.json').write_text(json.dumps(ledger, indent=2) + '\n')
    (out / 'census_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    with (out / 'frontier194.csv').open('w', newline='') as f:
        fields = ['canonical_class', 'strong_class', 'sha256', 'representative', 'quotient_states', 'table_file']
        w = csv.DictWriter(f, fieldnames=fields); w.writeheader()
        w.writerows({k: c[k] for k in fields} for c in ledger)
    print(json.dumps(summary, indent=2))


def verify(out, candidates):
    ledger = json.loads((out / 'frontier194.json').read_text())
    ordinary, broad = set(), set()
    for c in ledger:
        data = (out / c['table_file']).read_bytes()
        assert digest(data) == c['sha256']
        rows, states, start = parse(data)
        a, b = canonical(rows, states), canonical(rows, states, True)
        assert tuple_digest(a) == c['canonical_class'] and tuple_digest(b) == c['strong_class']
        assert len(states) == 194 and a not in ordinary
        assert quotient_count(rows, states) == c['quotient_states']
        ordinary.add(a); broad.add(b)
    results = []
    for p in candidates:
        data = p.read_bytes(); rows, states, start = parse(data)
        a, b = canonical(rows, states), canonical(rows, states, True)
        assert a is not None and b is not None
        results.append(dict(candidate=str(p), sha256=digest(data), working_states=len(states),
                            canonical_class=tuple_digest(a), strong_class=tuple_digest(b),
                            new_under_state_renaming=a not in ordinary, new_under_all_symmetries=b not in broad,
                            quotient_states=quotient_count(rows, states)))
    receipt = dict(status='PASS', historical_classes=len(ordinary), historical_strong_classes=len(broad),
                   candidate_results=results, proof_scope='Exact complete-tuple graph comparison only')
    print(json.dumps(receipt, indent=2))
    return receipt


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='command', required=True)
    p = sub.add_parser('build'); p.add_argument('repo', type=Path); p.add_argument('incoming', type=Path); p.add_argument('--out', type=Path, default=HERE)
    p = sub.add_parser('verify'); p.add_argument('candidates', type=Path, nargs='*'); p.add_argument('--out', type=Path, default=HERE); p.add_argument('--receipt', type=Path)
    a = ap.parse_args()
    if a.command == 'build':
        build(a.repo, a.incoming, a.out)
    else:
        r = verify(a.out, a.candidates)
        if a.receipt:
            a.receipt.write_text(json.dumps(r, indent=2) + '\n')
