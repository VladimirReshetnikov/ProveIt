#!/usr/bin/env python3
"""Reproduce the tree-and-spine and cycle-family checks. No dependencies."""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
import platform
from sparse_forms import (Arena, cycle_half, sparse_form, enumerate_small,
                           conway_order_table, simplest, canonical_tree,
                           leaf_labels)


def check_certificate(data: dict) -> None:
    """Rebuild from option IDs; do not trust cached values or metrics."""
    A = Arena()
    remap = {}
    for expected, row in enumerate(data['nodes']):
        assert row['id'] == expected
        assert all(j < expected for j in row['left'] + row['right'])
        node = A.make([remap[j] for j in row['left']],
                      [remap[j] for j in row['right']])
        assert node not in remap.values(), "Certificate failed extensionality"
        remap[expected] = node
        assert str(A.nodes[node].value) == row['value']
        assert A.nodes[node].height == row['height']
    assert len(A.reachable(remap[data['root']])) == len(data['nodes'])
    assert A.metrics(remap[data['root']]) == data['metrics']


def run(output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    examples = output.parent / 'examples'
    # 'output' is <package>/results; examples live in <package>/examples.
    examples.mkdir(exist_ok=True)
    result = {"python": platform.python_version(),
              "arithmetic": "exact fractions; structural interning; no floats",
              "status": "finite computational checks, not formal verification"}
    cycles = []
    for n in [3] + list(range(5, 65)):
        A, root = cycle_half(n)
        m = A.metrics(root)
        assert m['value'] == '1/2'
        assert m['vertices'] == m['edges'] == m['girth'] == n
        assert m['max_degree'] == 2
        check_certificate(A.certificate(root))
        cycles.append(m)
        if n in (3, 5, 6, 12):
            A.save(root, examples / f'half_cycle_{n}.json')
            (examples / f'half_cycle_{n}.dot').write_text(A.dot(root))
    result['cycle_family'] = {"count": len(cycles), "rows": cycles}

    A, root = cycle_half(5)
    table = conway_order_table(A)
    assert all(table[i][j] == (a.value <= b.value)
               for i, a in enumerate(A.nodes) for j, b in enumerate(A.nodes))
    half = A.canonical(Fraction(1, 2))
    table = conway_order_table(A)
    assert all(table[i][j] == (a.value <= b.value)
               for i, a in enumerate(A.nodes) for j, b in enumerate(A.nodes))
    assert table[root][half] and table[half][root]
    result['witness_comparison'] = {
        "pair_comparisons": len(A.nodes) ** 2,
        "equal_to_canonical_half_by_recursive_order": True,
        "witness": A.metrics(root)}

    samples = []
    for p in range(-64, 65):
        q = Fraction(p, 32)
        for target in (3, 4, 5, 8, 12):
            A, root, meta = sparse_form(q, target)
            m = A.metrics(root)
            assert A.nodes[root].value == q
            assert m['max_degree'] <= 3
            assert m['girth'] is None or m['girth'] >= target
            if not meta['integer_case']:
                assert m['vertices'] <= meta['vertex_bound']
                assert m['height'] <= meta['height_bound']
                assert m['vertices'] == meta['spine_vertices'] + meta['leaf_count'] - 1
                assert m['edges'] - m['vertices'] + 1 == meta['leaf_count'] - 1
            check_certificate(A.certificate(root))
            samples.append(dict(m, requested_girth=target))
    result['sparse_construction'] = {
        "count": len(samples), "values": "p/32 for -64 <= p <= 64",
        "requested_girths": [3, 4, 5, 8, 12],
        "maximum_vertices": max(r['vertices'] for r in samples),
        "maximum_height": max(r['height'] for r in samples),
        "planarity": "proved by construction; not separately software-tested",
        "rows": samples}

    showcase = []
    for q, g in [(Fraction(5, 8), 5), (Fraction(-11, 16), 8),
                 (Fraction(53, 32), 12), (Fraction(85, 256), 10)]:
        A, root, meta = sparse_form(q, g)
        check_certificate(A.certificate(root))
        assert A.metrics(root)['girth'] >= g
        name = f'sparse_{q.numerator}_{q.denominator}_g{g}'
        A.save(root, examples / f'{name}.json')
        (examples / f'{name}.dot').write_text(A.dot(root))
        showcase.append(dict(A.metrics(root), requested_girth=g, **{
            'leaf_count': meta['leaf_count'], 'vertex_bound': meta['vertex_bound']}))
    result['showcase'] = showcase

    EA, found, labelled = enumerate_small(5)
    small = []
    for n, roots in found.items():
        noninteger = [r for r in roots if EA.nodes[r].value.denominator > 1]
        triangle_free = [r for r in noninteger
                         if EA.metrics(r)['girth'] != 3]
        half_free = [r for r in triangle_free
                     if EA.nodes[r].value == Fraction(1, 2)]
        assert n >= 5 or not triangle_free
        small.append({'vertices': n, 'distinct_forms': len(roots),
                      'noninteger_forms': len(noninteger),
                      'triangle_free_noninteger_forms': len(triangle_free),
                      'triangle_free_half_forms': len(half_free)})
    assert small[-1]['triangle_free_half_forms'] > 0
    result['exhaustive_enumeration'] = {
        "maximum_vertices": 5, "valid_reachable_topological_labellings": labelled,
        "rows": small}

    # A separate exact recursion check for the Fibonacci leaf-count bound.
    f0, f1 = 0, 1
    fib = [f0, f1]
    for _ in range(15):
        fib.append(fib[-1] + fib[-2])
    leaf_rows = []
    for k in range(1, 9):
        counts = [len(leaf_labels(canonical_tree(Fraction(p, 2**k))))
                  for p in range(1, 2**k, 2)]
        assert max(counts) <= fib[k + 2]
        leaf_rows.append({'denominator_exponent': k,
                          'maximum_leaves': max(counts),
                          'fibonacci_bound': fib[k + 2]})
    result['leaf_counts'] = leaf_rows
    (output / 'sparse_results.json').write_text(json.dumps(result, indent=2) + '\n')
    lines = ['All checks passed.',
             f"Cycle certificates: {len(cycles)}.",
             f"Sparse grid certificates: {len(samples)}.",
             f"Additional showcase certificates: {len(showcase)}.",
             'Exhaustive unique-form counts:']
    lines += [str(r) for r in small]
    lines += ['Showcase metrics:'] + [str(r) for r in showcase]
    text = '\n'.join(lines) + '\n'
    (output / 'sparse_verification.txt').write_text(text)
    print(text)
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O: verification requires assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parent.parent / 'results')
    args = parser.parse_args()
    run(args.output)
