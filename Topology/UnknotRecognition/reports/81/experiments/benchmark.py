"""Paired complete supplied-sector timings with retained controls and limits.

Both arms enumerate the same nonlink standard-ray list.  ``prepared`` starts
from one shared prebuilt matching kernel; ``full`` rebuilds that kernel in
each timed call.  Source construction, expected-output derivation, canonical
digesting, independent coverage replay, and reporting serialization are
outside these timings.  Every complete output is checked after timing.

Each measured round randomizes baseline, planar, and a second identical
planar arm.  Ratios use matched complete pairs only.  Warmups and failed or
capped calls are retained.  A capped baseline warmup is not repeated and is
never assigned a speedup.  New-only capability rows are explicitly distinct.
These measurements concern supplied sectors, not a complete knot recognizer.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

from fixtures import double_capped_fibonacci, occupied, ray_digest


class DeadlineExpired(RuntimeError):
    pass


class Deadline:
    """The same clock policy for every timed arm, tested every 256 calls."""
    def __init__(self, seconds):
        self.expires = time.perf_counter()+seconds if seconds is not None else None
        self.calls = 0

    def __call__(self):
        self.calls += 1
        if self.expires is not None and self.calls % 256 == 1:
            if time.perf_counter() >= self.expires:
                raise DeadlineExpired('cooperative per-call deadline exceeded')


def digest_source(raw):
    data = json.dumps(raw, sort_keys=True, separators=(',', ':')).encode('utf-8')
    return sha256(data).hexdigest()


def cases_from_sources(args, corpus, audit):
    cases = []
    seen = set()

    def add(case):
        key = digest_source(case['triangulation']), tuple(map(tuple, case['allowed_types']))
        if key not in seen:
            seen.add(key)
            cases.append(case)

    for n in args.family_sizes:
        case = double_capped_fibonacci(n, (1, 1))
        case.update(kind='double-capped Fibonacci solid torus', family_n=n,
                    selection='all declared type-(1,1) sizes')
        add(case)
    for types in product(range(3), repeat=2):
        case = double_capped_fibonacci(2, types)
        case.update(kind='cap-type control', family_n=2,
                    selection='all nine cap choices at n=2, exact duplicates removed')
        add(case)
    indexed = {record['id']: record for record in audit['records']}
    requested = ('finite_trefoil', 'finite_trefoil_interior', 'finite_figureEight',
                 'finite_figureEight_interior', 'solid_torus_sum_rp3',
                 'solid_torus_sum_s2xs1', 'cap_1_2_3', 'interior_3_5')
    by_id = {record['id']: record for record in corpus['records']}
    for name in requested:
        record = by_id[name]
        candidates = [case for case in indexed[name]['cases']
                      if case['matching_nullity'] == 3]
        if not candidates:
            continue
        chosen = max(candidates, key=lambda item: (
            item['stats']['section_dimension'] == 2,
            item['stats']['potential_projections']//3, len(item['allowed_types']),
            item['ray_count'], item['allowed_types']))
        support = {tuple(pair) for pair in chosen['allowed_types']}
        reference = [surface['coordinates'] for surface in record['standard_vertices']
                     if occupied(surface['coordinates'])
                     and set(occupied(surface['coordinates'])) <= support]
        discs = sum(surface['essential_disc'] for surface in record['standard_vertices']
                    if occupied(surface['coordinates'])
                    and set(occupied(surface['coordinates'])) <= support)
        add(dict(id=name+'_selected_d3', kind='frozen finite triangulation',
                 source_id=name, triangulation=record['triangulation'],
                 allowed_types=chosen['allowed_types'],
                 reference_ray_count=len(reference), reference_ray_sha256=ray_digest(reference),
                 reference_essential_disc_rays=discs,
                 selection='max (polygon, retained classes, support size, rays, support) '
                           'among audited raw-nullity-three cases for this source'))
    for name, support in [('empty_sector', []), ('one_type_sector', [(0, 2)])]:
        case = double_capped_fibonacci(1, (1, 1))
        case.update(id=name, allowed_types=support, kind='small-query control',
                    selection='explicit empty or singleton support on n=1 double cap')
        add(case)
    if args.case_filter:
        cases = [case for case in cases if any(word in case['id']
                                               for word in args.case_filter)]
    return cases


def run_arm(case, kernel, protocol, arm, args):
    from fastunknot.normal_sector import build_sector_kernel, sector_rays, SearchLimit
    from fastunknot.sector_planar import sector_planar_rays
    stats, rays = {}, []
    started_utc = datetime.now(timezone.utc).isoformat()
    deadline = Deadline(args.seconds_per_call)
    start_wall, start_cpu = time.perf_counter(), time.process_time()
    error = None
    try:
        if protocol == 'full':
            active = build_sector_kernel(case['triangulation'], case['allowed_types'],
                                         check=deadline)
        else:
            active = kernel
        stats.update(active.stats)
        if arm == 'baseline':
            iterator = sector_rays(active, phase='standard', method='arrangement',
                                   check=deadline, max_bases=args.baseline_bases, stats=stats)
        else:
            iterator = sector_planar_rays(active, check=deadline, stats=stats)
        for ray in iterator:
            rays.append(ray)
        status = 'COMPLETE'
    except (DeadlineExpired, SearchLimit) as exc:
        status = 'INCONCLUSIVE_RESOURCE_LIMIT'
        error = str(exc)
    elapsed_cpu = time.process_time()-start_cpu
    elapsed_wall = time.perf_counter()-start_wall
    result = dict(arm=arm, protocol=protocol, status=status,
                  started_utc=started_utc, seconds=elapsed_wall, cpu_seconds=elapsed_cpu,
                  callback_calls=deadline.calls, stats=stats)
    if status == 'COMPLETE':
        result.update(ray_count=len(rays), ray_sha256=ray_digest(rays))
    else:
        result.update(reason=error, partial_rays=len(rays), ray_sha256=None)
    return result


def check_complete(call, expected):
    if call['status'] != 'COMPLETE':
        return expected
    observed = call['ray_count'], call['ray_sha256']
    if expected is None:
        return observed
    if expected != observed:
        raise AssertionError(('unequal complete output', expected, observed, call))
    return expected


def replay_case(case, kernel, expected, args):
    """Independent exhaustive replay outside all timing intervals."""
    from fastunknot.sector_planar import sector_planar_rays
    from fastunknot.sector_planar_verify import verify_planar_sector_certificate
    started = time.perf_counter()
    deadline = Deadline(args.replay_seconds)
    try:
        rays = list(sector_planar_rays(kernel, check=deadline))
        actual = len(rays), ray_digest(rays)
        if expected is not None and actual != expected:
            raise AssertionError(('independent-replay source list differs', actual, expected))
        proof = dict(schema='normal-sector-planar-rays-v1',
                     source_sha256=digest_source(case['triangulation']),
                     allowed_types=[list(pair) for pair in kernel.support],
                     quadrilateral_rays=sorted([rows[t][4+q] for t, q in kernel.support]
                                               for rows in rays))
        verification_stats = {}
        accepted = verify_planar_sector_certificate(case['triangulation'], proof,
                                                    check=deadline, stats=verification_stats)
        if not accepted:
            raise AssertionError(('independent complete-ray replay failed', case['id']))
        return dict(status='VERIFIED', seconds=time.perf_counter()-started,
                    certificate=proof, verifier_stats=verification_stats,
                    timing_scope='outside every enumeration timing')
    except DeadlineExpired as exc:
        return dict(status='INCONCLUSIVE_RESOURCE_LIMIT', reason=str(exc),
                    seconds=time.perf_counter()-started,
                    timing_scope='outside every enumeration timing')


def summarize(rounds):
    ratios, identical = [], []
    seconds = {'baseline': [], 'planar': [], 'planar_repeat': []}
    for record in rounds:
        by_arm = {call['arm']: call for call in record['calls']}
        for arm, call in by_arm.items():
            if call['status'] == 'COMPLETE':
                seconds[arm].append(call['seconds'])
        old, new, repeat = (by_arm.get(arm) for arm in seconds)
        if old and new and old['status'] == new['status'] == 'COMPLETE':
            ratios.append(old['seconds']/new['seconds'])
        if new and repeat and new['status'] == repeat['status'] == 'COMPLETE':
            identical.append(new['seconds']/repeat['seconds'])
    return dict(complete_paired_rounds=len(ratios),
        median_paired_ratio=statistics.median(ratios) if ratios else None,
        paired_ratios=ratios, identical_planar_ratios=identical,
        median_identical_ratio=statistics.median(identical) if identical else None,
        medians={arm: statistics.median(values) if values else None
                 for arm, values in seconds.items()})


def write_json(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2)+'\n')


def run(args):
    sys.path.insert(0, str(args.fast.resolve()))
    from fastunknot.normal_sector import build_sector_kernel
    from fastunknot.sector_planar import sector_planar_rays
    corpus_bytes = args.corpus.read_bytes()
    audit_bytes = args.audit.read_bytes()
    corpus, audit = json.loads(corpus_bytes), json.loads(audit_bytes)
    cases = cases_from_sources(args, corpus, audit)
    result = dict(schema='planar-sector-paired-benchmark-v1', mode=args.mode,
                  benchmark_scope=__doc__, baseline_commit=args.commit,
                  python=platform.python_version(), platform=platform.platform(),
                  started_utc=datetime.now(timezone.utc).isoformat(),
                  corpus_sha256=sha256(corpus_bytes).hexdigest(),
                  audit_sha256=sha256(audit_bytes).hexdigest(),
                  seconds_per_call=args.seconds_per_call,
                  baseline_bases=args.baseline_bases,
                  callback_policy='same cooperative clock test every 256 callbacks',
                  small_repeats=args.small_repeats, large_repeats=args.large_repeats,
                  source_files={}, cases=[], capacity=[])
    for name in ('normal_sector.py', 'normal_surface_geometry.py', 'sector_planar.py'):
        path = args.fast/'fastunknot'/name
        result['source_files'][name] = sha256(path.read_bytes()).hexdigest()
    for name in ('fixtures.py', 'benchmark.py'):
        path = Path(__file__).parent/name
        result['source_files']['experiments/'+name] = sha256(path.read_bytes()).hexdigest()
    if args.mode != 'capacity':
        for case in cases:
            prepare_start = time.perf_counter()
            kernel = build_sector_kernel(case['triangulation'], case['allowed_types'])
            preparation = time.perf_counter()-prepare_start
            row = dict(case, source_sha256=digest_source(case['triangulation']),
                       matching_nullity=len(kernel.basis), kernel_stats=kernel.stats,
                       untimed_shared_kernel_preparation_seconds=preparation, protocols=[])
            if len(kernel.basis) > 3:
                raise AssertionError(('unsupported selected case', case['id']))
            expected = None
            if 'reference_ray_sha256' in case:
                expected = case['reference_ray_count'], case['reference_ray_sha256']
            for protocol in ('prepared', 'full'):
                record = dict(protocol=protocol, warmup=[], rounds=[])
                rng = random.Random('planar-benchmark-v1:'+case['id']+':'+protocol)
                for arm in ('baseline', 'planar'):
                    call = run_arm(case, kernel, protocol, arm, args)
                    expected = check_complete(call, expected)
                    record['warmup'].append(call)
                    print('WARMUP', case['id'], protocol, arm, call['status'],
                          f"{call['seconds']:.6f}s", flush=True)
                baseline_finished = record['warmup'][0]['status'] == 'COMPLETE'
                count = (args.large_repeats if case.get('family_n', 0) >= 16
                         else args.small_repeats)
                if args.mode == 'preflight':
                    count = 0
                record['baseline_repeated'] = baseline_finished
                if not baseline_finished:
                    record['baseline_note'] = 'No repeats or ratio after capped warmup'
                for number in range(count):
                    order = ['planar', 'planar_repeat']
                    if baseline_finished:
                        order.append('baseline')
                    rng.shuffle(order)
                    calls = []
                    for arm in order:
                        call = run_arm(case, kernel, protocol, arm, args)
                        expected = check_complete(call, expected)
                        calls.append(call)
                    record['rounds'].append(dict(number=number, order=order, calls=calls))
                record['summary'] = summarize(record['rounds'])
                row['protocols'].append(record)
                print('RESULT', case['id'], protocol, record['summary'], flush=True)
            row.update(expected_ray_count=expected[0] if expected else None,
                       expected_ray_sha256=expected[1] if expected else None)
            if args.mode != 'preflight':
                row['independent_replay'] = replay_case(case, kernel, expected, args)
                print('REPLAY', case['id'], row['independent_replay']['status'],
                      row['independent_replay']['seconds'], flush=True)
            result['cases'].append(row)
            write_json(args.output, result)
    if args.mode == 'capacity' or args.with_capacity:
        for n in args.capacity_sizes:
            case = double_capped_fibonacci(n, (1, 1))
            deadline = Deadline(args.capacity_seconds)
            start = time.perf_counter()
            stats = {}
            try:
                kernel = build_sector_kernel(case['triangulation'], case['allowed_types'],
                                             check=deadline)
                built = time.perf_counter()
                rays = list(sector_planar_rays(kernel, check=deadline, stats=stats))
                stopped = time.perf_counter()
                row = dict(id=case['id'], source_sha256=digest_source(case['triangulation']),
                           status='COMPLETE', build_seconds=built-start,
                           enumeration_seconds=stopped-built, total_seconds=stopped-start,
                           kernel_stats=kernel.stats, stats=stats,
                           ray_count=len(rays), ray_sha256=ray_digest(rays))
                row['independent_replay'] = replay_case(
                    case, kernel, (len(rays), ray_digest(rays)), args)
            except DeadlineExpired as exc:
                row = dict(id=case['id'], source_sha256=digest_source(case['triangulation']),
                           status='INCONCLUSIVE_RESOURCE_LIMIT', reason=str(exc),
                           total_seconds=time.perf_counter()-start, stats=stats)
            row.update(comparison='new-only capability; no baseline run and no ratio',
                       seconds_allowance=args.capacity_seconds)
            result['capacity'].append(row)
            write_json(args.output, result)
            print('CAPACITY', row, flush=True)
    result['finished_utc'] = datetime.now(timezone.utc).isoformat()
    write_json(args.output, result)
    print('COMPLETE', args.output, flush=True)


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, default=root/'fixtures/discovery_corpus.json')
    parser.add_argument('--audit', type=Path, default=root/'results/corpus_audit.json')
    parser.add_argument('--mode', choices=('preflight', 'paired', 'capacity'), default='paired')
    parser.add_argument('--family-sizes', nargs='+', type=int, default=[1, 2, 4, 8, 16, 32])
    parser.add_argument('--capacity-sizes', nargs='+', type=int, default=[64, 128, 256])
    parser.add_argument('--case-filter', nargs='+')
    parser.add_argument('--small-repeats', type=int, default=5)
    parser.add_argument('--large-repeats', type=int, default=3)
    parser.add_argument('--seconds-per-call', type=float, default=15.0)
    parser.add_argument('--capacity-seconds', type=float, default=90.0)
    parser.add_argument('--replay-seconds', type=float, default=30.0)
    parser.add_argument('--baseline-bases', type=int)
    parser.add_argument('--with-capacity', action='store_true')
    parser.add_argument('--commit', default='8188525b70033dcfe7c51ea5ae2c8723ad0c0198')
    args = parser.parse_args()
    if min(args.small_repeats, args.large_repeats) < 1:
        parser.error('repeat counts must be positive')
    if args.seconds_per_call <= 0 or args.capacity_seconds <= 0:
        parser.error('deadline allowances must be positive')
    run(args)
