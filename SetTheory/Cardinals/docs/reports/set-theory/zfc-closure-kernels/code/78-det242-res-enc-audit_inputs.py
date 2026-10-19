#!/usr/bin/env python3
"""Audit saved search dictionaries against the complete finite source AST.

This checks grammar word identities and expands source paths. It does not
construct or validate a Turing machine, its initialization, or runtime.
"""
from collections import Counter
import json
from exact_exchange import load_context, HERE

old, roots, allowed, groups, expr, root, atoms, locks = load_context()
records = {}
for name in ['baseline_fine_grammar.json', 'search_control.json',
             'search_baseline.json', 'search_reduced_locks.json', 'search_zero5.json']:
    data = json.loads((HERE/name).read_text())
    grammar = {w:(l,r) for w,l,r in data['rules']}
    for word, (left, right) in grammar.items():
        assert word == left + right
        assert left not in allowed or allowed[left]&1
        assert right not in allowed or allowed[right]&2
        assert all(c in grammar or c in allowed for c in (left,right))
    routes = {(r['source'], r['read']):r['word'] for r in data['routes']}
    route_checks = [(routes[s,b], p, t) for s,b,w,cs in groups for p,t in cs]
    def matches(word, path, target):
        for bit in path:
            if word not in grammar:
                return False
            word = grammar[word][int(bit)]
        return word == target
    assert all(matches(*c) for c in route_checks)
    full_lock_failures = [c for c in locks if not matches(*c)]
    histogram = Counter()
    maximum_depth = 0
    ancestors = set()
    def ew(i, path):
        global maximum_depth
        e = expr[i]
        if e[0] == 'L':
            maximum_depth = max(maximum_depth, len(path))
            histogram[max(map(len, path.split('1')))] += 1
        elif e[0] == 'W':
            ww(e[1], path)
        else:
            ew(e[1], path+'0'); ew(e[2], path+'1')
    def ww(word, path):
        assert word not in ancestors, 'Recursive expanded source'
        ancestors.add(word)
        if word in allowed:
            ew(atoms[word], path)
        else:
            left, right = grammar.get(word, old.get(word))
            ww(left, path+'0'); ww(right, path+'1')
        ancestors.remove(word)
    ew(root, '')
    records[name] = dict(roles=len(grammar), source_leaves=sum(histogram.values()),
                         maximum_depth=maximum_depth,
                         maximum_zero_run=max(histogram),
                         leaves_with_six_consecutive_zeros=sum(v for k,v in histogram.items() if k>=6),
                         zero_run_histogram=dict(sorted(histogram.items())),
                         route_checks=len(route_checks),
                         original_bootstrap_lock_failures=len(full_lock_failures))
(HERE/'input_audit.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
