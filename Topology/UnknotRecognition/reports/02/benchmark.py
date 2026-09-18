"""Reproduce actual small-case measurements; no asymptotic inference is made."""
from __future__ import annotations
import json
from pathlib import Path
import platform
import sys
from time import perf_counter
from unknotlab import fox_determinant
from unknotlab.khovanov import reduced_khovanov
from unknotlab.recognize import parse_input, recognize
from unknotlab.normal import one_tetrahedron_solid_torus


def main() -> None:
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'examples' / 'manifest.json').read_text())
    rows = []
    for entry in manifest:
        data = json.loads((root / 'examples' / entry['file']).read_text())
        diagram = parse_input(data)
        start = perf_counter()
        result = recognize(diagram)
        default_seconds = perf_counter() - start
        start = perf_counter()
        homology = reduced_khovanov(diagram, check_d_squared=True)
        checked_homology_seconds = perf_counter() - start
        if result.status != entry['expected_status']:
            raise AssertionError(f'Wrong default answer for {entry["file"]}')
        if homology.is_unknot != (entry['expected_status'] == 'unknot'):
            raise AssertionError(f'Wrong homology answer for {entry["file"]}')
        rows.append({'file': entry['file'], 'crossings': diagram.crossings,
                     'expected_status': entry['expected_status'],
                     'default_status': result.status, 'default_method': result.method,
                     'determinant': fox_determinant(diagram),
                     'reduced_F2_rank': homology.total_rank,
                     'cube_states': homology.cube_states, 'generators': homology.generators,
                     'd_squared_checked': homology.d_squared_checked,
                     'elimination_xors': homology.elimination_xors,
                     'default_seconds': default_seconds,
                     'checked_homology_seconds': checked_homology_seconds})
    t = one_tetrahedron_solid_torus()
    factor = 10 ** 1000
    start = perf_counter()
    surface = t.dual_surface([3 * factor, -factor, -2 * factor])
    surface_seconds = perf_counter() - start
    summary = {'python': sys.version, 'platform': platform.platform(),
               'complete_backend_complexity': '2^O(n), not quasi-polynomial',
               'measurements_are_not_complexity_proofs': True,
               'examples': rows,
               'compressed_surface': {'scale': '10^1000', 'tetrahedra': 1,
                                      'disc_count': '3*10^1000',
                                      'euler_characteristic': '10^1000',
                                      'coordinate_bits': surface.coordinate_bits,
                                      'seconds': surface_seconds}}
    target = root / 'results' / 'benchmark.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(summary, indent=2) + '\n')
    print(f'Wrote {target}; {len(rows)} example diagrams all classified correctly.')
    for row in rows:
        print(f'{row["file"]:30} n={row["crossings"]:2} '
              f'det={row["determinant"]:2} Kh={row["reduced_F2_rank"]:2} '
              f'C={row["generators"]:5} {row["checked_homology_seconds"]:.6f}s')


if __name__ == '__main__':
    main()
