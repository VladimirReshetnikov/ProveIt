"""Check the three edge-link formulas underlying the all-t Fibonacci proof.

The verifier-owned raw-cell path produces the tested attaching words.
The closed forms are independently generated here from the displayed
three-case mathematical formula.  Finite checks supplement its proof.
"""

import argparse
import json
from pathlib import Path

from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.source_handle_reduction import reduce_source_handles
from normal_orbit_research.fixtures import layered_torus, fibonacci
from unused_handles import decompose_unused_handles, verify_unused_handle_certificate


def expected_word(size, index):
    a = lambda i: 2 * i + 1   # Signed integer words use id+1.
    b = lambda i: 2 * i + 2
    c = 2 * size - 1
    if index <= size - 4:
        return [b(index), a(index + 1), a(index + 2),
                -b(index + 2), -b(index + 1), -a(index)]
    if index == size - 3:
        return [b(index), a(index + 1), c, -b(index + 1), -a(index)]
    return [b(index), c, c, -a(index)]


def cyclic_form(word):
    if not word:
        return ()
    inverse = [-value for value in reversed(word)]
    return min(tuple(candidate[i:] + candidate[:i])
               for candidate in (word, inverse) for i in range(len(word)))


def run():
    records = []
    for size in (*range(1, 13), 16, 32, 64, 128):
        raw, _ = layered_torus(size)
        prepared = _prepare(raw, lambda: None)
        zero = _coordinates(prepared, [[0] * 7 for _ in raw['tetrahedra']], lambda: None)
        core = _reference_parallelity(prepared, zero, lambda: None)['core']
        one = {item['id']: item for item in core['handles1']}
        actual = {}
        for item in core['handles2']:
            word = []
            for sector in item['cycle']:
                if sector['dimension'] != 1:
                    continue
                handle = sector['handle']
                face = one[handle]
                forward = (sector['tetrahedron'], sector['face']) == (face['tetrahedron'], face['face'])
                word.append((1 if forward else -1) * (handle + 1))
            actual[item['edge']] = cyclic_form(word)
        expected = {6 * index + 5: cyclic_form(expected_word(size, index))
                    for index in range(size - 1)}
        if actual != expected:
            raise AssertionError(('edge-link formula', size))
        old = reduce_source_handles(raw, record_certificate=True)
        moves = [dict(kind='cancel_12', one_handle=2 * i, two_handle=6 * i + 5)
                 for i in range(size - 1)]
        if old['moves'] != moves:
            raise AssertionError(('queue formula', size))
        dual = old['compressing_disc']['boundary_witness']['dual_values']
        expected_dual = [value for i in range(size - 1)
                         for value in (fibonacci(size - i + 1), 0)] + [1]
        if dual != expected_dual:
            raise AssertionError(('dual Fibonacci formula', size))
        new = decompose_unused_handles(raw)
        if not verify_unused_handle_certificate(raw, new['certificate']):
            raise AssertionError(('new source replay', size))
        records.append(dict(tetrahedra=size, source_edge_links_checked=len(actual),
                            native_queue_checked=True, native_dual_formula_checked=True,
                            new_source_replay=True,
                            dual_bits=sum(max(1, abs(value).bit_length()) for value in dual)))
    return dict(schema='unused-handle-fibonacci-audit-v1', records=records,
                total_edge_links=sum(r['source_edge_links_checked'] for r in records),
                limitation='Finite checks supplement the three-local-type induction; they are not its proof.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(len(result['records']), 'sources;', result['total_edge_links'], 'edge-link rows; all passed')
