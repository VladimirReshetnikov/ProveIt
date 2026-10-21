#!/usr/bin/env python3
"""Audit a finite projection basis extracted from the accepted Source149 proof.

The Source149 forward checker is retained byte-for-byte except a possible final
newline; this file adds a separate restricted-leaf census. No proof search runs.
The source theorem is ordinary mathematics, not a proof-assistant endpoint.
"""
import hashlib
import json
from pathlib import Path
import sys
from itertools import product

import check_classical_compact as original

ALLOWED = ('', 'L', 'R', 'LL', 'RR', 'LLR', 'RRR', 'LLRR')


def audit(path):
    full = original.check(path)
    data = json.loads(Path(path).read_text())
    terms = original.Terms()
    ids = []
    for item in data['term_table']:
        if item == 'T':
            node = terms.T
        elif isinstance(item, dict):
            node = terms.var(item['var'])
        else:
            node = terms.imp(ids[item[0]], ids[item[1]])
        ids.append(node)

    def project(a, word):
        for letter in word:
            # For template leaves a projection is traversed only through a
            # displayed implication or T=I(T,T). It is never guessed below a
            # schema variable. Literal zero therefore respects the native alias.
            if a != terms.T and terms.items[a][0] != 'I':
                return None
            a = terms.parts(a)[0 if letter == 'L' else 1]
        return a

    rows = []
    leaf_inputs = []
    counts = {'zero': 0, **{word or 'epsilon': 0 for word in ALLOWED}}
    for node in data['nodes']:
        if node['rule']['kind'] != 'dominated_rho8':
            continue
        formula = ids[node['term']]
        pre, post = terms.parts(formula)
        cu, a = terms.parts(pre)
        c, u = terms.parts(cu)
        ac, bc = terms.parts(post)
        aa, cc = terms.parts(ac)
        b, ccc = terms.parts(bc)
        assert a == aa and c == cc == ccc
        if u == terms.T:
            selected = 'zero'
        else:
            candidates = [word for word in ALLOWED if project(a, word) == u]
            assert candidates, ('projection not covered', node['id'])
            selected = candidates[0] or 'epsilon'
        counts[selected] += 1
        rows.append({'node': node['id'], 'projection': selected})
        leaf_inputs.append((a, u))

    def displayed_paths(a, u, prefix=''):
        if a == u:
            return [prefix]
        if terms.items[a][0] != 'I':
            return []
        left, right = terms.parts(a)
        return displayed_paths(left, u, prefix + 'L') + displayed_paths(right, u, prefix + 'R')

    witnesses = []
    for number in [0, 1, 2, 5, 31, 113, 115, 1112, 2163, 3639]:
        pre, _ = terms.parts(ids[data['nodes'][number]['term']])
        cu, a = terms.parts(pre)
        _, u = terms.parts(cu)
        witnesses.append({'node': number, 'constant_zero': u == terms.T,
                          'displayed_paths': displayed_paths(a, u)})
    forced = {'', 'L', 'R', 'LL', 'LLR'}
    alternatives = [set(w['displayed_paths']) for w in witnesses if w['node'] in [115, 1112, 2163]]
    assert all(s and not (s & forced) for s in alternatives)
    assert all(not (alternatives[i] & alternatives[j]) for i in range(3) for j in range(i))
    optimal_covers = []
    for choices in product(*(sorted(s) for s in alternatives)):
        selected = forced | set(choices)
        if all(u == terms.T or any(project(a, word) == u for word in selected)
               for a, u in leaf_inputs):
            words = sorted(selected, key=lambda w: (len(w), w))
            prefix_closure = {word[:i] for word in words for i in range(len(word) + 1)}
            optimal_covers.append({
                'functions': ['zero'] + [word or 'epsilon' for word in words],
                'projection_trie_nodes_including_root': len(prefix_closure),
                'projection_trie_edges': len(prefix_closure) - 1,
                'unselected_intermediate_prefixes': sorted(prefix_closure - selected),
            })
    assert len(optimal_covers) == 6
    assert min(c['projection_trie_nodes_including_root'] for c in optimal_covers) == 8
    assert len(rows) == 1260
    assert data['roots']['rho8'] == 3727
    return {
        'verified': True,
        'claim': 'Truth and MP with the nine computed-fourth-argument rho8 families derive every unrestricted rho8 instance.',
        'source_certificate_sha256': hashlib.sha256(Path(path).read_bytes()).hexdigest(),
        'projection_order': ['zero'] + [p or 'epsilon' for p in ALLOWED],
        'leaf_counts': counts,
        'literal_cover_minimum': {
            'functions_including_constant_zero': 9,
            'proof': 'Five mandatory singleton paths, three pairwise disjoint nonempty path-choice sets disjoint from those paths, and one constant-zero-only leaf.',
            'witnesses': witnesses,
            'all_six_optimal_covers': optimal_covers,
            'scope': 'Minimum number of fixed displayed-subterm projections plus constant zero that cover this unchanged certificate. Not a lower bound for other proofs or calculi.',
        },
        'forward_proof': full,
        'leaves': rows,
        'limits': 'Numerical calculus equivalence only. No source compilation, state saving, binary startup, or new Lean/Rocq proof.',
    }


if __name__ == '__main__':
    certificate = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('dominated_rho8_full_certificate.json')
    result = audit(certificate)
    output = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(__file__).with_name('projection_basis_audit.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'leaves'}, indent=2))
