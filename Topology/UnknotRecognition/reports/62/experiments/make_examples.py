#!/usr/bin/env python3
"""Produce complete, replayable examples and the attachment counterexample."""
import json
import bootstrap
from fastunknot.integer_codec import json_safe
from fastunknot.sparse_incidence import analyze_sparse_port_incidence
from fastunknot.sparse_signed_incidence import analyze_signed_sparse_port_incidence


def main():
    n, rows, ports = 12, [[0, 1, 10, 11, 1]], [[(0, 3)], [(2, 6)], [(6, 9)]]
    example = dict(size=n, pairings=rows, ports=ports,
                   result=analyze_sparse_port_incidence(n, rows, ports, record_certificate=True))
    (bootstrap.ROOT / 'examples' / 'unsigned.json').write_text(
        json.dumps(json_safe(example), indent=2) + '\n')
    rows = [[0, 2, 0, 2, -1, 1]]
    signed = dict(size=3, signed_pairings=rows, ports=[[(0, 3)]],
                  result=analyze_signed_sparse_port_incidence(
                      3, rows, [[(0, 3)]], record_certificate=True))
    (bootstrap.ROOT / 'examples' / 'signed.json').write_text(
        json.dumps(json_safe(signed), indent=2) + '\n')
    barrier = dict(size=4, ports=[[[0, 2]], [[2, 4]]],
                   first_pairings=[[0, 1, 2, 3, 1]],
                   second_pairings=[[0, 1, 2, 3, -1]],
                   common_histogram=[[3, 2]],
                   attachment=[[0, 1, 2, 3, 1]],
                   after_attachment=dict(first_orbit_count=2, second_orbit_count=1))
    (bootstrap.ROOT / 'examples' / 'gluing_obstruction.json').write_text(json.dumps(barrier, indent=2) + '\n')


if __name__ == '__main__':
    main()
