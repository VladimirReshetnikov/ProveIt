"""Paired timings for actual binary normal-surface disc queries.

No result is a complete knot-recognition timing. Each measured call includes
source validation, certificate production, and independent replay. Timings
are run serially with randomized arm order and identical A/A controls.
"""

import argparse
import hashlib
import json
import platform
import random
from pathlib import Path
from statistics import median
from time import perf_counter

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from normal_orbit_research.fixtures import layered_torus


SEED = 261009032


def run_arm(triangulation, coordinates, arm):
    begin = perf_counter()
    if arm.startswith('core'):
        answer = normal_compressing_disk_count(triangulation, coordinates,
                                               record_certificate=True)
        middle = perf_counter()
        valid = verify_normal_disk_count_certificate(triangulation, coordinates,
                                                     answer['certificate'])
    else:
        mode = 'coordinates' if arm == 'full_coordinates' else 'disk'
        answer = normal_component_census(triangulation, coordinates, mode=mode,
                                         record_certificate=True)
        middle = perf_counter()
        valid = verify_normal_component_certificate(triangulation, coordinates,
                                                    answer['certificate'])
    end = perf_counter()
    if not valid:
        raise AssertionError('measured independent verification failed')
    return answer, dict(produce=middle-begin, verify=end-middle, total=end-begin)


def source_hashes():
    root = Path(__file__).resolve().parents[1]
    names = ['weighted_orbits.py', 'weighted_orbit_verify.py',
             'normal_component_geometry.py', 'normal_surface_components.py',
             'normal_component_verify.py', 'normal_disk_kernel.py',
             'interval_orbits.py', 'interval_orbit_verify.py',
             'normal_surface_geometry.py']
    return {name: hashlib.sha256((root/'fastunknot'/name).read_bytes()).hexdigest()
            for name in names}


def case(kind, parameter, repeats, rng):
    if kind == 'dimension':
        tetrahedra = parameter
        triangulation, coordinates = layered_torus(tetrahedra)
        arms = ['three_weights', 'three_weights_control', 'full_coordinates']
        expected = 1
    else:
        tetrahedra = 16
        triangulation, meridian = layered_torus(tetrahedra)
        factor, collar = 1 << parameter, (1 << parameter)+1
        coordinates = [[factor*value+(collar if j < 4 else 0)
                        for j, value in enumerate(row)] for row in meridian]
        arms = ['three_weights', 'core', 'core_control']
        expected = factor
    metadata = {}
    for arm in arms:
        answer, _ = run_arm(triangulation, coordinates, arm)
        assert answer['compressing_disk_components'] == expected
        proof_bytes = len(json.dumps(json_safe(answer['certificate']),
                                    sort_keys=True, separators=(',', ':')).encode())
        metadata[arm] = dict(stats=answer['stats'], certificate_bytes=proof_bytes,
            core_coordinate_bits=answer.get('core_coordinate_bits'),
            weight_dimension=answer.get('weight_dimension', 3))
    samples = []
    for repeat in range(repeats):
        order = arms.copy()
        rng.shuffle(order)
        sample = dict(repeat=repeat, order=order, timings={})
        for arm in order:
            answer, timing = run_arm(triangulation, coordinates, arm)
            assert answer['compressing_disk_components'] == expected
            sample['timings'][arm] = timing
        samples.append(sample)
    summary = {arm: {field: median(s['timings'][arm][field] for s in samples)
                      for field in ('produce', 'verify', 'total')} for arm in arms}
    pairs = ([('full_coordinates', 'three_weights'),
              ('three_weights', 'three_weights_control')] if kind == 'dimension' else
             [('three_weights', 'core'), ('core', 'core_control')])
    ratios = {f'{old}/{new}': median(s['timings'][old]['total']/s['timings'][new]['total']
                                    for s in samples) for old, new in pairs}
    print(kind, parameter, {key: round(value, 3) for key, value in ratios.items()}, flush=True)
    return dict(kind=kind, parameter=parameter, tetrahedra=tetrahedra,
                input_coordinate_bits=max(value.bit_length() for row in coordinates for value in row),
                expected_compressing_discs=expected, triangulation=triangulation,
                coordinates=coordinates, metadata=metadata, samples=samples,
                medians=summary, paired_median_ratios=ratios)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--repeats', type=int, default=7)
    parser.add_argument('--max-tetrahedra', type=int, default=128)
    parser.add_argument('--max-bits', type=int, default=32768)
    args = parser.parse_args()
    rng = random.Random(SEED)
    records = []
    report = dict(seed=SEED, python=platform.python_version(), platform=platform.platform(),
                  baseline_commit='7518823550fbc8c217bc8be0113fe52002e77465',
                  source_hashes=source_hashes(), repeats=args.repeats, records=records,
                  scope='supplied normal-vector queries with mandatory independent replay; '
                        'not whole knot recognition')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for kind, parameters, ceiling in [('dimension', [4,8,16,32,64,128], args.max_tetrahedra),
                                      ('core', [64,512,4096,32768], args.max_bits)]:
        for parameter in parameters:
            if parameter <= ceiling:
                records.append(case(kind, parameter, args.repeats, rng))
                args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')


if __name__ == '__main__':
    main()
