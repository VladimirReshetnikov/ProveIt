#!/usr/bin/env python3
"""Finite equality screen on the 128 grammar words and 44 inherited atoms.

The affine matrices are checked semantically by the separate source-program
certifier.  This script checks only the displayed finite algebraic quotient.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import json

from fine_semantic_domain import Domain, trace_normal


def matrix_product(a, b):
    n = len(a)
    assert len(b) == n and all(len(row) == n for row in a + b)
    return [[sum(a[i][k] * b[k][j] for k in range(n))
             for j in range(n)] for i in range(n)]


def screen(package, affine_file):
    d = Domain(package)
    g = json.loads((Path(package) / 'grammar.json').read_text())
    words = [d.expand(w) for w, _, _ in g['rules']]
    words += list(d.expansions.values())
    assert len(words) == 172
    affine = json.loads(Path(affine_file).read_text())
    pairs = {tuple(sorted(p)) for p in affine['independent_pairs']}
    assert len(pairs) == 178 and d.disjoint_pairs <= pairs
    matrices = {c: v['matrix'] for c, v in affine['linear_atoms'].items()}
    assert len(matrices) == 22
    identity = [[int(i == j) for j in range(10)] for i in range(10)]

    def run_key(w):
        out, current, active = [], identity, False
        for c in w:
            if c in matrices:
                current = matrix_product(matrices[c], current)
                active = True
            else:
                if active:
                    out.append(('matrix', tuple(map(tuple, current))))
                out.append(('opaque', c))
                current, active = identity, False
        if active:
            out.append(('matrix', tuple(map(tuple, current))))
        return tuple(out)

    result = {}
    quotients = {
        'exact_fine_words': lambda w: w,
        'disjoint_support_traces': lambda w: trace_normal(w, d.disjoint_pairs),
        'affine_extended_traces': lambda w: trace_normal(w, pairs),
        'consecutive_affine_run_products': run_key,
    }
    for name, key in quotients.items():
        classes = defaultdict(list)
        for w in words:
            classes[key(w)].append(w)
        result[name] = {'classes': len(classes),
                        'collisions': [v for v in classes.values() if len(v) > 1]}
    return {
        'status': 'PASS_FINITE_ALGEBRAIC_SCREEN',
        'grammar_words': 128,
        'inherited_atoms': 44,
        'quotients': result,
        'scope': 'Only these 172 words and four sufficient equality relations '
                 'were checked. The affine matrices require the separate '
                 'source-program proof. Distinct quotient keys do not imply '
                 'different program semantics or any state lower bound.',
    }


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--package', type=Path, required=True)
    p.add_argument('--affine', type=Path, required=True)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    assert __debug__, 'Assertions must remain enabled.'
    result = screen(a.package, a.affine)
    text = json.dumps(result, indent=2) + '\n'
    if a.output:
        a.output.write_text(text)
    print(text, end='')
