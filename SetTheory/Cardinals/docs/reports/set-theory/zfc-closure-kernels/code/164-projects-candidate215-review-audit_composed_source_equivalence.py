#!/usr/bin/env python3
"""Standalone all-branch source-CFG comparison for the composed K215 source.

This checker imports neither the source builder nor the binary runtime.
It independently resolves every primitive edge twice: (1) by ordinal subtree
intervals and (2) by the binary-address counter equations.  Equality of these
graphs is an all-natural register-program bisimulation, not a finite run test.

Usage: python -B audit_composed_source_equivalence.py REFERENCE.json CANDIDATE.json OUTPUT.json
"""
import hashlib
import json
from collections import Counter
from pathlib import Path
import sys


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    raw = Path(path).read_bytes()
    rows = json.loads(raw)
    leaves = {}
    prefixes = set()
    for p, op, arg in rows:
        assert set(p) <= {'0', '1'} and p not in leaves
        assert op in ('CI', 'CD', 'CB', 'CC', 'CH')
        assert (arg is None) if op == 'CH' else (isinstance(arg, int) and arg >= 0)
        if op in ('CB', 'CC'):
            assert arg >= 1
        leaves[p] = (op, arg)
        prefixes.update(p[:j] for j in range(len(p)+1))
    traversal = []
    subtrees = set()
    def visit(p):
        if p in leaves:
            assert p+'0' not in prefixes and p+'1' not in prefixes
            t = leaves[p]
            traversal.append([p, *t])
        else:
            assert p+'0' in prefixes and p+'1' in prefixes
            t = (visit(p+'0'), visit(p+'1'))
        subtrees.add(t)
        return t
    visit('')
    assert traversal == rows
    metrics = {
        'primitive_occurrences': len(rows),
        'guarded_cases': sum(2 if op == 'CD' else 1 for _, op, _ in rows),
        'dag_nodes': len(subtrees),
        'maximum_depth': max(len(p) for p, _, _ in rows),
        'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1')),
        'primitive_counts': dict(sorted(Counter(op for _, op, _ in rows).items()))
    }
    return raw, rows, metrics


def graph_by_intervals(rows):
    n = len(rows)
    intervals = {}
    for i, (p, _, _) in enumerate(rows):
        for j in range(len(p)+1):
            prefix = p[:j]
            if prefix not in intervals:
                intervals[prefix] = [i, i+1]
            else:
                intervals[prefix][1] = i+1
    def branch_target(p, bit, k):
        ancestors = [j for j, b in enumerate(p) if b == bit]
        if len(ancestors) < k:
            return 0
        enclosing = p[:ancestors[-k]]
        start, end = intervals[enclosing]
        return (end if bit == '0' else start) % n
    graph = []
    for i, (p, op, arg) in enumerate(rows):
        following = (i+1) % n
        if op == 'CI':
            targets = (following,)
        elif op == 'CD':
            targets = (branch_target(p, '0', 1), following)
        elif op == 'CB':
            targets = (branch_target(p, '0', arg),)
        elif op == 'CC':
            targets = (branch_target(p, '1', arg),)
        else:
            targets = ()
        graph.append((op, arg if op in ('CI', 'CD') else None, targets))
    return graph


def graph_by_binary_addresses(rows):
    ordinal = {p: i for i, (p, _, _) in enumerate(rows)}
    depth = max(map(len, ordinal))
    def dispatch(address):
        extended = address + '0'*(depth+1)
        for end in range(len(extended)+1):
            prefix = extended[:end]
            if prefix in ordinal:
                assert '1' not in address[end:]
                return ordinal[prefix]
        raise AssertionError('Address does not dispatch to a leaf')
    def successor(address):
        if not address:
            return ''
        value = (int(address, 2)+1) % (1 << len(address))
        return format(value, f'0{len(address)}b')
    def truncate(address, bit, k):
        seen = 0
        for j in range(len(address)-1, -1, -1):
            if address[j] == bit:
                seen += 1
                if seen == k:
                    return address[:j]
        return ''
    graph = []
    for p, op, arg in rows:
        if op == 'CI':
            targets = (dispatch(successor(p)),)
        elif op == 'CD':
            targets = (dispatch(successor(truncate(p, '0', 1))), dispatch(successor(p)))
        elif op == 'CB':
            targets = (dispatch(successor(truncate(p, '0', arg))),)
        elif op == 'CC':
            targets = (dispatch(truncate(p, '1', arg)),)
        else:
            targets = ()
        graph.append((op, arg if op in ('CI', 'CD') else None, targets))
    return graph


def main():
    if not __debug__:
        raise RuntimeError('This checker requires enabled assertions; do not use -O.')
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    reference, candidate, output = sys.argv[1:]
    descriptions = []
    graphs = []
    for path in (reference, candidate):
        raw, rows, metrics = load(path)
        first = graph_by_intervals(rows)
        second = graph_by_binary_addresses(rows)
        assert first == second, 'Independent edge resolvers disagree'
        descriptions.append({'path': path, 'sha256': digest(raw), 'metrics': metrics})
        graphs.append(first)
    assert graphs[0] == graphs[1], 'Resolved primitive graphs differ'
    compact = (json.dumps(graphs[0], separators=(',', ':'))+'\n').encode()
    result = {
        'status': 'PASS_ALL_PRIMITIVE_GUARDED_SOURCE_EQUIVALENCE',
        'reference': descriptions[0],
        'candidate': descriptions[1],
        'identical_guarded_cases': descriptions[0]['metrics']['guarded_cases'],
        'cfg_sha256': digest(compact),
        'resolvers': ['ordinal subtree intervals', 'binary-address arithmetic'],
        'decrement_target_order': ['zero: branch, no register change', 'positive: decrement, continue'],
        'preserved_semantics': ['increment register', 'decrement register and both branches',
                                'every constant jump target', 'literal halting occurrence'],
        'theorem': 'Identity of primitive ordinal and register tuple is a step-for-step bisimulation for every natural register tuple, from ordinal0 or any corresponding ordinal.',
        'calibration_dependency': 'Reviewed public Permuted210 source theorem, with theorem-safe seed and cofinal enumeration beyond every finite cutoff.',
        'scope_exclusions': ['No binary-state-count certification', 'No binary runtime or blank-startup proof',
                             'No new proof-assistant mechanization of inherited ZFC calibration']
    }
    Path(output).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
