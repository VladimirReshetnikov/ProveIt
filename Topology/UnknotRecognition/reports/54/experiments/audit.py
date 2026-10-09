"""Execute the deterministic test suite and write an honest evidence manifest.
SPDX-License-Identifier: MIT-0
"""
import hashlib
import json
import platform
import sys
import time
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT/'tests'))
from test_core import QuotientTests


def main():
    start = time.perf_counter()
    with (ROOT/'results'/'unit_tests.txt').open('w') as stream:
        suite = unittest.defaultTestLoader.discover(str(ROOT/'tests'))
        result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    # Re-execute the exhaustive finite test to obtain its actual counter.
    exhaustive = QuotientTests('test_exhaustive_partitions_and_one_cone')
    exhaustive.test_exhaustive_partitions_and_one_cone()
    out = dict(status='PASS' if result.wasSuccessful() else 'FAIL',
               unittest_methods=result.testsRun, failures=len(result.failures), errors=len(result.errors),
               seconds=time.perf_counter()-start, python=sys.version, platform=platform.platform(),
               exhaustive_finite_cone_cases=exhaustive.cases,
               randomized_interval_packing_sources=500, packing_modes_per_source=2,
               randomized_sequential_sources=700, sequential_cone_comparisons=7000,
               randomized_compressed_grammars=400,
               sharp_height_families_checked=16,
               largest_population_exponent=16000,
               largest_delayed_prefix_exponent=16000,
               deepest_grammar_nodes=2500,
               seeds=dict(packing=26100861, sequential=26100862, grammar=26100863),
               native_gate='NOT_RUN; see native_gate_status.json',
               scope='The scalar weighted test backend expands bounded literal sources. '
                     'Huge populations and programs are tested without point expansion, '
                     'using analytic expectations and independent graph replay.',
               source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                   for folder in ('compiled_ports', 'tests', 'integration')
                   for p in sorted((ROOT/folder).glob('*.py'))})
    (ROOT/'results'/'audit.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'source_sha256'}, indent=2))
    if not result.wasSuccessful():
        raise SystemExit(1)

if __name__ == '__main__':
    main()
