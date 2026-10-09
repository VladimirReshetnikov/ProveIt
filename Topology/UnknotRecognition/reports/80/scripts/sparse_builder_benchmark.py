"""Paired complete sector-construction timings with a geometry-cache control.

python sparse_builder_benchmark.py --fast-root PATH --output OUTPUT.json
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import statistics
import sys
import time
from unittest.mock import patch


def measurements(arms, rounds):
    result = {name: [] for name in arms}
    for repeat in range(rounds):
        order = list(arms) if repeat % 2 == 0 else list(reversed(arms))
        for name in order:
            start = time.perf_counter()
            arms[name]()
            result[name].append(time.perf_counter()-start)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    sys.path.insert(0, str(args.fast_root.resolve()))
    from fastunknot.normal_sector import build_sector_kernel
    from fastunknot.sector_sparse import PreparedSectorSource, build_sparse_sector_kernel
    from normal_orbit_research.fixtures import layered_torus
    records = []
    for tetrahedra in (64, 256, 1024):
        raw, _ = layered_torus(tetrahedra)
        start = time.perf_counter()
        source = PreparedSectorSource(raw)
        preparation = time.perf_counter()-start
        for width in (1, 8, 32):
            support = [(j*tetrahedra//width, 2) for j in range(width)]
            arms = {'baseline': lambda: build_sector_kernel(raw, support),
                    'sparse_one_shot': lambda: build_sparse_sector_kernel(raw, support),
                    'sparse_reused': lambda: source.build(support)}
            kernels = {name: run() for name, run in arms.items()}
            for field in ('corner_class', 'classes', 'groups', 'matrix', 'potentials',
                          'cycle_rows', 'basis'):
                assert len({repr(getattr(kernel, field)) for kernel in kernels.values()}) == 1
            samples = measurements(arms, args.rounds)

            def cached_prepare(triangulation, check):
                check()
                return source.prepared

            with patch('fastunknot.normal_sector._prepare', new=cached_prepare):
                control = {'baseline_cached': lambda: build_sector_kernel(raw, support),
                           'sparse_reused_control': lambda: source.build(support)}
                samples.update(measurements(control, args.rounds))
            medians = {name: statistics.median(values) for name, values in samples.items()}
            stats = kernels['sparse_reused'].stats
            record = dict(t=tetrahedra, k=width, prepare_seconds=preparation,
                          measurements=samples, medians=medians,
                          reuse_speedup=medians['baseline']/medians['sparse_reused'],
                          one_shot_speedup=medians['baseline']/medians['sparse_one_shot'],
                          cached_baseline_speedup=(medians['baseline_cached'] /
                                                   medians['sparse_reused_control']),
                          old_dense_label_entries=stats['precompiled_equations']*width,
                          sparse_dense_label_entries=stats['dense_label_entries'])
            records.append(record)
            print(tetrahedra, width,
                  {name: round(value*1000, 3) for name, value in medians.items()}, flush=True)
    names = ['fastunknot/normal_sector.py', 'fastunknot/sector_sparse.py',
             'normal_orbit_research/fixtures.py']
    result = dict(
        scope='Complete sector construction, including unchanged rational elimination. '
              'Baseline and one-shot arms include validation; reused construction uses '
              'one previously validated source. Synthetic genuine layered-solid-torus '
              'triangulations with supplied sparse supports; no whole-knot speed claim.',
        cache_control='The extra baseline_cached arm substitutes only the previously '
                      'validated geometry for baseline _prepare. Both control arms '
                      'therefore reuse geometry; no production baseline API is changed.',
        python=platform.python_version(), rounds=args.rounds, records=records,
        source_sha256={name: sha256((args.fast_root/name).read_bytes()).hexdigest()
                       for name in names})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
