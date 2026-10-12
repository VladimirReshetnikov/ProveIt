"""Paired pinned-arrangement versus exact-envelope enumeration measurements.

Fixture construction and output serialization/hashing are outside timed
regions.  Reused-kernel and full-build calls are measured separately.  Each
paired cohort retains one warm-up and five AB/BA rounds by default.  One
eight-tetrahedron-base case includes duplicate A/A arms.  All outputs must
agree exactly.  Timing is not a worst-case complexity proof.
"""

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

from fastunknot.sector_envelope import sector_envelope_rays
from .fixtures import capped_fibonacci, ray_digest


FAST = Path(__file__).resolve().parents[1]
BASELINE_COMMIT = '66098968e88bba797143ac1bf7ad0ac4c5f697df'
BASELINE_FILE = Path(__file__).with_name('baseline_normal_sector.py')


def load_baseline():
    name = 'fastunknot._sector_envelope_pinned_baseline'
    spec = importlib.util.spec_from_file_location(name, BASELINE_FILE)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def source_hashes():
    names = ['fastunknot/normal_sector.py', 'fastunknot/sector_envelope.py',
             'sector_envelope_research/baseline_normal_sector.py',
             'sector_envelope_research/fixtures.py', 'sector_envelope_research/benchmark.py']
    return {name: sha256((FAST / name).read_bytes()).hexdigest() for name in names}


def summarize(rounds, field):
    old = [row['arms']['old'][field] for row in rounds]
    new = [row['arms']['new'][field] for row in rounds]
    ratios = [a / b for a, b in zip(old, new)]
    return dict(old_median_ns=statistics.median(old),
                new_median_ns=statistics.median(new),
                paired_speedup_median=statistics.median(ratios),
                paired_speedup_min=min(ratios), paired_speedup_max=max(ratios))


def run(repeats, capacity):
    if repeats < 1:
        raise ValueError('repeats must be positive')
    baseline = load_baseline()
    pins = source_hashes()
    rng = random.Random(202610092)
    cases = [(n, typ) for n in (1, 4, 8, 16, 32) for typ in (1, 2)]
    cases += [(n, 0) for n in (8, 16, 32)]
    result = dict(schema='sector-envelope-benchmark-v1', python=platform.python_version(),
                  platform=platform.platform(), timer='time.perf_counter_ns',
                  baseline_commit=BASELINE_COMMIT, source_sha256=pins,
                  repeats=repeats, description=__doc__, cases=[], capacity=[])
    started = time.perf_counter()
    for n, typ in cases:
        fixture = capped_fibonacci(n, typ)
        raw, allowed = fixture['triangulation'], fixture['allowed_types']
        kernel_started = time.perf_counter_ns()
        shared = baseline.build_sector_kernel(raw, allowed)
        kernel_elapsed = time.perf_counter_ns() - kernel_started
        case = dict(base_tetrahedra=n, tetrahedra=n + 1, cap_type=typ,
                    kernel_stats=shared.stats, setup_kernel_ns=kernel_elapsed, scopes={})
        reference = None

        def measure(arm, scope):
            nonlocal reference
            stats = {}
            before = time.perf_counter_ns()
            kernel = baseline.build_sector_kernel(raw, allowed) if scope == 'full' else shared
            after_build = time.perf_counter_ns()
            if arm.startswith('old'):
                rays = list(baseline.sector_rays(kernel, phase='standard',
                                               method='arrangement', stats=stats))
            else:
                rays = list(sector_envelope_rays(kernel, stats=stats))
            after = time.perf_counter_ns()
            digest = ray_digest(rays)
            if reference is None:
                reference = digest
            assert digest == reference, (n, typ, arm, scope)
            return dict(total_ns=after - before, build_ns=after_build - before,
                        enumeration_ns=after - after_build, ray_sha256=digest,
                        ray_count=len(rays), stats=stats)

        for scope in ('reused_kernel', 'full'):
            order = ['old', 'new']
            rng.shuffle(order)
            warmup = dict(order=order.copy(), arms={})
            for arm in order:
                warmup['arms'][arm] = measure(arm, scope)
            rounds = []
            for index in range(repeats):
                if index % 2:
                    order = list(reversed(warmup['order']))
                else:
                    order = warmup['order'].copy()
                if n == 8 and typ == 1:
                    order += [arm + '_AA' for arm in reversed(order)]
                row = dict(round=index, order=order.copy(), arms={})
                for arm in order:
                    row['arms'][arm] = measure(arm, scope)
                rounds.append(row)
                print('PAIR', n, typ, scope, index,
                      round(row['arms']['old']['total_ns'] / 1e9, 6),
                      round(row['arms']['new']['total_ns'] / 1e9, 6), flush=True)
            case['scopes'][scope] = dict(warmup=warmup, rounds=rounds,
                                         summary=summarize(rounds, 'total_ns'))
        result['cases'].append(case)
    for n in capacity:
        fixture = capped_fibonacci(n, 1)
        before = time.perf_counter_ns()
        kernel = baseline.build_sector_kernel(fixture['triangulation'],
                                             fixture['allowed_types'])
        after_build = time.perf_counter_ns()
        stats = {}
        rays = list(sector_envelope_rays(kernel, stats=stats))
        after = time.perf_counter_ns()
        result['capacity'].append(dict(base_tetrahedra=n, tetrahedra=n + 1,
            cap_type=1, total_ns=after - before, build_ns=after_build - before,
            enumeration_ns=after - after_build, ray_sha256=ray_digest(rays),
            ray_count=len(rays), stats=stats, scope='new only; no speedup comparison'))
        print('CAPACITY', n, (after - before) / 1e9, flush=True)
    assert pins == source_hashes(), 'timed source changed during benchmark'
    result['seconds'] = time.perf_counter() - started
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--capacity', type=int, nargs='*', default=[64, 128, 256])
    args = parser.parse_args()
    result = run(args.repeats, args.capacity)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('COMPLETE', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
