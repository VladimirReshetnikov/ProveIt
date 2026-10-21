#!/usr/bin/env python3
"""Independent literal-source binding audit for transfer-pop/cache-return.

This checks exact construction, both source CFG resolvers, and the preservation
of every internal AX successor including its sole exterior continuation.
The all-natural compiler proof is in cache_transfer_review.md; this is not a
binary allocation or runtime certificate.
"""
from pathlib import Path
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'machine'
AUDIT = HERE
spec = importlib.util.spec_from_file_location('source_language', HERE.parent / 'code/source_language.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)


def induced_graph(rows, prefix):
    graph = s.graph_intervals(rows)
    inside = [i for i, (path, _, _) in enumerate(rows) if path.startswith(prefix)]
    assert inside == list(range(inside[0], inside[-1] + 1))
    lo, hi = inside[0], inside[-1] + 1
    result, exterior = [], set()
    for i in inside:
        effect, targets = graph[i]
        mapped = []
        for j in targets:
            if lo <= j < hi:
                mapped.append(j - lo)
            else:
                exterior.add(j)
                mapped.append('exterior')
        result.append([effect, mapped])
    assert len(exterior) == 1
    exit_ordinal = exterior.pop()
    assert rows[exit_ordinal][1:] == ['CB', 1]
    return result, rows[exit_ordinal][0]


def main():
    raw = (BASE / 'sites215.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
    oldrows = json.loads(raw)
    p = s.tree(oldrows)
    clear = (('CD', 1), ('CC', 1))
    copy = s.subtree(p, '1101011')
    drop = s.subtree(p, '110101')
    nip = s.subtree(p, '111')
    for block in (clear, copy, drop, nip):
        assert s.boundary(block)[:2] == (0, 0)
    cache = s.replace(p, '11010010111', (('CD', 4), (('CI', 5), ('CC', 2))))
    three = s.replace(cache, '11010', s.subtree(cache, '11010010'))
    bodies = {
        'direct-left': ((clear, copy), nip),
        'direct-right': (clear, (copy, nip)),
        'DNN-left': ((drop, nip), nip),
        'DNN-right': (drop, (nip, nip)),
    }
    old_axiom, old_exit = induced_graph(oldrows, '1101001001')
    results = {}
    expanded = []
    for base_name, body in bodies.items():
        root = s.replace(three, '111', body)
        expanded.append((base_name, root, body, False))
        mp = s.subtree(root, '110101')
        swapped = s.replace(s.replace(root, '110101', body), '111', mp)
        expanded.append((base_name + '-swap01', swapped, body, True))
    for name, expected, body, swap in expanded:
        filename = AUDIT / ('sites-cachetransfer-' + name + '.json')
        actual_raw = filename.read_bytes()
        rows = json.loads(actual_raw)
        actual = s.tree(rows)
        assert expected == actual
        assert s.graph_intervals(rows) == s.graph_arithmetic(rows)[0]
        assert s.subtree(actual, '1101001') == s.subtree(p, '1101001001')
        assert s.subtree(actual, '111' if swap else '110101') == s.subtree(cache, '110100101')
        assert s.boundary(body) == (0, 0, True)
        axiom, new_exit = induced_graph(rows, '1101001')
        assert axiom == old_axiom
        results[name] = {
            'sha256': hashlib.sha256(actual_raw).hexdigest(),
            'source_metrics': s.metrics(actual),
            'literal_regeneration': True,
            'two_CFG_resolvers_agree': True,
            'AX_all_4565_internal_effects_and_successors_preserved': True,
            'AX_old_exit_CB1_path': old_exit,
            'AX_new_exit_CB1_path': new_exit,
            'S_body_closed': True,
            'wire_fields': {'S': [1 if swap else 0], 'MP(x)': [0 if swap else 1, 'x'], 'AX(c;x,y)': ['c+2', 'y', 'x']},
        }
    receipt = {
        'status': 'PASS',
        'scope': 'Literal source binding and CFG audit; ordinary all-natural compiler proof is separate; no binary allocation claimed.',
        'baseline_sha256': hashlib.sha256(raw).hexdigest(),
        'wire_fields': {'S': ['0'], 'MP(x)': ['1', 'x'], 'AX(c;x,y)': ['c+2', 'y', 'x']},
        'variants': results,
    }
    (HERE / 'cache_transfer_review_results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
