#!/usr/bin/env python3
"""Run small verified examples using the bundled pinned native source."""

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path[:0] = [str(ROOT / 'code'), str(ROOT / 'native_snapshot')]

from fastunknot import Diagram
from normal_orbit_research.fixtures import layered_torus
from unused_handles import compile_diagram_initial_core, verify_diagram_initial_core
from native_moments import normal_parallelity_moment_words
from native_moments_verify import verify_native_moment_words


def main():
    for name, diagram in [
        ('one-crossing unknot', Diagram.from_braid(2, [1])),
        ('trefoil', Diagram.from_braid(2, [1, 1, 1])),
    ]:
        result = compile_diagram_initial_core(diagram)
        assert verify_diagram_initial_core(diagram, result['certificate'])
        summary = {'example': name, 'status': result['status'], 'verified': True}
        if result['status'] == 'ADMISSIBLE_CORE':
            core = result['retained_core']
            summary['core_handle_counts'] = {
                key: len(core[key]) for key in ('zero_handles', 'one_handles', 'two_handles')}
        print(json.dumps(summary))
    source, coordinates = layered_torus(2)
    result = normal_parallelity_moment_words(source, coordinates, record_certificate=True)
    assert result['status'] == 'COMPLETE'
    assert verify_native_moment_words(source, coordinates, result['certificate'])
    print(json.dumps({'example': 'native boundary first returns', 'status': result['status'],
                      'ports': len(result['skeleton']['ports']),
                      'gap_lengths': [g['unmarked_edges'] for g in result['skeleton']['gaps']],
                      'verified': True}))


if __name__ == '__main__':
    main()
