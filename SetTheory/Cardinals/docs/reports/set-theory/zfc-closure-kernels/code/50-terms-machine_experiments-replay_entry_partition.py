#!/usr/bin/env python3
"""Independently replay the exact assignment partition of an entry search.

This checks the search-space definition, traversal, every branch/pruning
weight, and the final frontier. It does not independently verify the symbolic
executor's semantics or rerun its reported failed traces.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import itertools
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--result', required=True, type=Path)
    parser.add_argument('--table', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    assert __debug__, 'Assertions must remain enabled'
    result = json.loads(args.result.read_text())
    degree = result['degree']
    table = {}
    for line in args.table.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, t = line.split()
        key = int(q), int(b)
        assert key not in table
        table[key] = int(w), direction, int(t)
    states = sorted({q for q, _ in table})
    assert len(states) == 252 and len(table) == 504
    canonical = ('#! start 64\n' + ''.join(
        f'{q} {b} {w} {direction} {t}\n' for (q, b), (w, direction, t)
        in sorted(table.items()))).encode()
    table_sha256 = hashlib.sha256(canonical).hexdigest()
    assert table_sha256 == '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
    protected_states = {0, 1, 2, 3, 4, 6, 28, 31, 38, 40, 43, 44, 48, 56,
                        59, 60, 63, 64, 69, 73, 75, 83, 85, 95, 97, 109, 112, 131}
    protected = {(q, b) for q in protected_states for b in (0, 1)} - {(3, 0)}
    targets = {table[key][2] for key in protected}
    eligible = [q for q in states if q not in {64, 96} and q not in targets
                and all((q, b) not in protected for b in (0, 1))]
    incoming = {q: sorted(k for k, v in table.items() if v[2] == q and k[0] != q)
                for q in eligible}
    family = [q for q in eligible if len(incoming[q]) == degree]
    assert len(family) == (131 if degree == 1 else 46)
    supplied_family = [group['deleted_state'] for group in result['groups']]
    if len(supplied_family) == 1:
        family = [q for q in family if q == supplied_family[0]]
    family.sort(key=lambda q: (q not in {204, 107}, q))
    assert family == supplied_family
    domains = {q: list(itertools.product((0, 1), ('L', 'R'),
                                         [str(t) for t in states + [254] if t != q]))
               for q in family}
    for group in result['groups']:
        q = group['deleted_state']
        assert group['incoming_rows'] == [[str(s), b] for s, b in incoming[q]]
        assert group['planned'] == 1008 ** degree
    stack = [(q, {}) for q in reversed(family)]
    counts = Counter()
    pruned = Counter()
    node_counts = Counter()
    survivors = []
    failures = Counter()
    journal_file = args.result.parent / result['journal']['file']
    compressed = not journal_file.exists()
    if compressed:
        journal_file = Path(str(journal_file) + '.gz')
    opener = gzip.open if compressed else open
    digest, journal_bytes = hashlib.sha256(), 0
    with opener(journal_file, 'rb') as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
            journal_bytes += len(chunk)
    assert journal_bytes == result['journal']['bytes']
    assert digest.hexdigest() == result['journal']['sha256']
    with opener(journal_file, 'rt') as journal:
        for line in journal:
            entry = json.loads(line)
            q, assigned = stack.pop()
            assert q == entry['deleted_state']
            encoded = {str(i): list(action) for i, action in assigned.items()}
            assert encoded == entry['assigned_actions']
            outcome = entry['outcome']
            counts[outcome] += 1
            node_counts[q] += 1
            if outcome in {'branch', 'branch_unused'}:
                i = entry['incoming_index']
                assert 0 <= i < degree and i not in assigned
                for action in reversed(domains[q]):
                    stack.append((q, {**assigned, i: action}))
            elif outcome == 'prune':
                expected = 1008 ** (degree - len(assigned))
                assert entry['completions'] == expected
                assert 0 <= entry['first_failure_case'] < 8391
                assert entry['reason'] in {'fuel', 'unsupported_symbolic_rule', 'missing_transition'}
                pruned[q] += expected
                failures[entry['reason']] += 1
            elif outcome == 'affine_survivor':
                assert len(assigned) == degree
                survivors.append(entry)
            else:
                raise AssertionError(('unknown journal outcome', outcome))
    frontier = [{'deleted_state': q,
                 'assigned_actions': {str(i): list(v) for i, v in assigned.items()},
                 'completions': 1008 ** (degree - len(assigned))}
                for q, assigned in reversed(stack)]
    assert result['frontier'] == frontier
    assert result['remaining'] == sum(f['completions'] for f in frontier)
    assert result['nodes'] == sum(node_counts.values())
    assert result['pruned'] == sum(pruned.values())
    assert result['survivors'] == survivors
    assert result['failures'] == dict(failures)
    assert result['planned'] == len(family) * 1008 ** degree
    assert result['planned'] == result['pruned'] + len(survivors) + result['remaining']
    for group in result['groups']:
        q = group['deleted_state']
        assert group['nodes'] == node_counts[q]
        assert group['pruned'] == pruned[q]
        assert group['survivors'] == sum(e['deleted_state'] == q for e in survivors)
    assert (result['status'] == 'completed') == (len(stack) == 0)
    report = {'status': 'PASS', 'scope': __doc__, 'degree': degree,
              'table_sha256': table_sha256,
              'planned': result['planned'], 'pruned': result['pruned'],
              'remaining': result['remaining'], 'frontier_nodes': len(frontier),
              'journal_nodes': sum(node_counts.values()), 'outcomes': dict(counts),
              'result_sha256': hashlib.sha256(args.result.read_bytes()).hexdigest(),
              'journal_sha256': result['journal']['sha256'],
              'auditor_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
