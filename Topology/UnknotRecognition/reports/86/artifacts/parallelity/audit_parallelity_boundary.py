"""Run the focused tests and save counts, pins, and two complete example proofs."""

import argparse
from hashlib import sha256
import io
import json
from pathlib import Path
import subprocess
from time import perf_counter
import unittest

import fastunknot
from fastunknot.integer_codec import json_safe
from test_parallelity_boundary import ParallelityBoundaryTests


def audit(destination):
    began = perf_counter()
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=True)
    statistics = dict(finite_literal_comparisons=0, source_authenticated_comparisons=0,
                      largest_literal_corner_universe=0)
    examples = {}
    source_checked = ParallelityBoundaryTests.checked_source
    geometry_checked = ParallelityBoundaryTests.checked_geometry

    def checked_geometry(self, geometry):
        result = geometry_checked(self, geometry)
        statistics['finite_literal_comparisons'] += 1
        statistics['largest_literal_corner_universe'] = max(
            statistics['largest_literal_corner_universe'], geometry['corner_points'])
        return result

    def checked_source(self, triangulation, coordinates):
        source, result, plan = source_checked(self, triangulation, coordinates)
        statistics['source_authenticated_comparisons'] += 1
        key = None
        if (plan['relative_two_handles'] and len(coordinates) == 2
            and result['interface']['port_count'] == 8 and 'full_circle' not in examples):
            key = 'full_circle'
        elif (len(coordinates) == 2 and plan['isolated_balls'] == 2
              and result['interface']['port_count'] == 2
              and not plan['relative_one_handles'] and not plan['relative_two_handles']
              and 'partial_collar' not in examples):
            key = 'partial_collar'
        if key:
            examples[key] = dict(triangulation=triangulation, coordinates=coordinates,
                                 source_parallelity_certificate=source['certificate'],
                                 boundary_certificate=result['certificate'],
                                 local_relative_handle_plan=plan)
        return source, result, plan

    ParallelityBoundaryTests.checked_geometry = checked_geometry
    ParallelityBoundaryTests.checked_source = checked_source
    stream = io.StringIO()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ParallelityBoundaryTests)
    try:
        result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    finally:
        ParallelityBoundaryTests.checked_geometry = geometry_checked
        ParallelityBoundaryTests.checked_source = source_checked
    (destination/'tests.txt').write_text(stream.getvalue())
    if not result.wasSuccessful():
        print(stream.getvalue())
        raise RuntimeError('focused parallelity interface tests failed')
    here = Path(__file__).resolve().parent
    source_root = Path(fastunknot.__file__).resolve().parents[2]
    pin = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source_root,
                                  text=True).strip()
    source_files = ['fast/fastunknot/normal_parallelity.py',
                    'fast/fastunknot/normal_parallelity_geometry.py',
                    'fast/fastunknot/normal_parallelity_verify.py',
                    'fast/fastunknot/weighted_orbits.py',
                    'fast/fastunknot/weighted_orbit_verify.py']
    generated = []
    for name, example in sorted(examples.items()):
        file = destination/(name+'.json')
        file.write_text(json.dumps(json_safe(example), sort_keys=True, indent=2)+'\n')
        generated.append(dict(name=name, file=file.name,
                              sha256=sha256(file.read_bytes()).hexdigest(),
                              tetrahedra=len(example['coordinates']),
                              ports=example['boundary_certificate']['interface']['port_count']))
    output = dict(status='PASS', test_methods=result.testsRun,
                  failures=len(result.failures), errors=len(result.errors),
                  tests_seconds=perf_counter()-began, source_commit=pin,
                  large_binary_multiplicity_exponent=8192,
                  synthetic_disc_markings=126, **statistics,
                  prototype_sha256={file.name: sha256(file.read_bytes()).hexdigest()
                                    for file in sorted(here.glob('*.py'))},
                  maintained_source_sha256={name: sha256((source_root/name).read_bytes()).hexdigest()
                                            for name in source_files}, examples=generated,
                  scope='ordered interfaces and local relative-handle plans only; no knot verdict')
    (destination/'audit.json').write_text(json.dumps(output, sort_keys=True, indent=2)+'\n')
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    audit(parser.parse_args().output)
