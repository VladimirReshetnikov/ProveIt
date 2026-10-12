"""Paired complete planar-sector enumeration with incumbent controls.

Run from the fast directory:

    python -m planar_sector_research.benchmark --output results.json \
        --prior-envelope PATH/fastunknot/sector_envelope.py

Fixture construction, source/output hashing, invariants, and report writing
are outside every timed region.  Complete construction arms include their
native geometry preparation and exact rational elimination.  Post-construction
arms share exactly one read-only kernel built by the incumbent constructor.
Every yielded surface is natively validated inside the enumerator's lift.
The per-arm allowance is cooperative wall time, not a hard process timeout.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import importlib.util
import json
from math import comb
from pathlib import Path
import platform
import statistics
import sys
import time

from fastunknot.integer_codec import json_safe
from fastunknot.normal_sector import _source_hash, build_sector_kernel, sector_rays
from fastunknot.sector_planar import sector_planar_rays
from fastunknot.sector_sparse import build_sparse_sector_kernel

from .family_audit import formula_rows, parameter_rays
from .fixtures import capped_fibonacci, double_capped_fibonacci, ray_digest, vector_key


class ArmLimit(RuntimeError):
    """A cooperative benchmark allowance expired; no completeness follows."""


class Budget:
    def __init__(self, seconds):
        self.deadline = time.perf_counter()+seconds
        self.calls = 0

    def __call__(self):
        self.calls += 1
        if time.perf_counter() >= self.deadline:
            raise ArmLimit('cooperative per-arm wall-time allowance exhausted')


def kernel_digest(kernel):
    """Fingerprint all producer-visible algebraic data, outside timing."""
    material = (kernel.support, kernel.corner_class, kernel.classes, kernel.groups,
                kernel.matrix, tuple(sorted(kernel.potentials.items())),
                kernel.cycle_rows, kernel.basis)
    return sha256(repr(material).encode('ascii')).hexdigest()


def load_prior(path):
    name = 'fastunknot._prior_envelope'
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError('prior envelope module cannot be loaded')
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def execute_arm(arm, raw, support, shared_kernel, allowance, prior=None):
    """Time construction (when requested), enumeration and native lift checks."""
    rays, stats, kernel = [], {}, None
    budget = Budget(allowance)
    started = time.perf_counter()
    cpu_started = time.process_time()
    status, reason, stage = 'COMPLETE', None, 'construction'
    try:
        if arm == 'incumbent_full':
            kernel = build_sector_kernel(raw, support, check=budget)
        elif arm == 'planar_full':
            kernel = build_sparse_sector_kernel(raw, support, check=budget)
        else:
            kernel = shared_kernel
        stats.update(kernel.stats)
        stage = 'enumeration'
        if arm in ('incumbent_full', 'incumbent_postkernel'):
            generator = sector_rays(kernel, method='auto', check=budget, stats=stats)
        elif arm == 'prior_envelope_postkernel':
            generator = prior.sector_envelope_rays(kernel, check=budget, stats=stats)
        else:
            generator = sector_planar_rays(kernel, check=budget, stats=stats)
        for rows in generator:
            rays.append(rows)
        budget()
    except ArmLimit as exc:
        status, reason = 'RESOURCE_LIMIT', str(exc)
    cpu_seconds = time.process_time()-cpu_started
    seconds = time.perf_counter()-started
    # Hashing and every assertion below are outside the timed region.
    result = dict(arm=arm, status=status, reason=reason, interrupted_stage=(
                  None if status == 'COMPLETE' else stage),
                  seconds=seconds, cpu_seconds=cpu_seconds, allowance_seconds=allowance,
                  callback_calls=budget.calls, ray_count=len(rays),
                  ray_sha256=ray_digest(rays), stats=stats,
                  kernel_sha256=None if kernel is None else kernel_digest(kernel))
    return result, rays


def check_result(record, rays, expected, expected_sha, shared_sha, *, n=None):
    if len({vector_key(ray) for ray in rays}) != len(rays):
        raise AssertionError(('duplicate emitted ray', record['arm']))
    if record['kernel_sha256'] is not None and record['kernel_sha256'] != shared_sha:
        raise AssertionError(('constructor algebraic mismatch', record['arm']))
    if record['status'] != 'COMPLETE':
        record['complete_output_matches_formula'] = None
        return
    if len(rays) != len(expected) or record['ray_sha256'] != expected_sha:
        raise AssertionError(('complete ray list differs from explicit formula', record))
    if {vector_key(ray) for ray in rays} != {vector_key(ray) for ray in expected}:
        raise AssertionError('ray digest equality did not agree with exact vector equality')
    record['complete_output_matches_formula'] = True
    stats = record['stats']
    if stats['emitted_rays'] != len(expected):
        raise AssertionError('incorrect emitted-ray counter')
    if (n is not None and record['arm'].startswith('incumbent_')
            and stats['method'] == 'arrangement'):
        formulas = dict(hyperplanes=2*n+6,
                        positive_directions=(n+1)**2+3,
                        nonextreme_directions=(n-1)*(n+3),
                        bases_attempted=comb(2*n+6, 2))
        if any(stats[key] != value for key, value in formulas.items()):
            raise AssertionError(('incumbent work-count formula mismatch', n, stats, formulas))
        record['incumbent_work_formulas_checked'] = True


def paired_round(arms, index, warmup, raw, support, shared, allowance, prior,
                 expected, expected_sha, shared_sha, n):
    order = list(arms) if warmup or index % 2 == 0 else list(reversed(arms))
    results = []
    for arm in order:
        record, rays = execute_arm(arm, raw, support, shared, allowance, prior)
        check_result(record, rays, expected, expected_sha, shared_sha, n=n)
        if kernel_digest(shared) != shared_sha:
            raise AssertionError('shared post-construction kernel was mutated')
        record.update(round=None if warmup else index, warmup=warmup)
        results.append(record)
        print('n=', n if n is not None else len(raw['tetrahedra'])-1,
              'warmup' if warmup else f'round={index}', arm,
              record['status'], f'{record["seconds"]:.6f}s',
              'rays=', record['ray_count'], flush=True)
    return results


def summaries(warmups, rounds, pairs):
    arms = [record['arm'] for record in warmups]
    by_arm = {}
    for arm in arms:
        samples = [next(record for record in records if record['arm'] == arm)
                   for records in rounds]
        complete = all(sample['status'] == 'COMPLETE' for sample in samples)
        by_arm[arm] = dict(
            complete_rounds=sum(sample['status'] == 'COMPLETE' for sample in samples),
            total_rounds=len(samples),
            median_seconds=statistics.median(sample['seconds'] for sample in samples)
            if complete else None,
            median_cpu_seconds=statistics.median(sample['cpu_seconds'] for sample in samples)
            if complete else None)
    comparisons = {}
    for name, (old, new) in pairs.items():
        ratios = []
        all_complete = all(record['status'] == 'COMPLETE' for record in warmups
                           if record['arm'] in (old, new))
        for records in rounds:
            selected = {record['arm']: record for record in records}
            if all(selected[arm]['status'] == 'COMPLETE' for arm in (old, new)):
                ratios.append(selected[old]['seconds']/selected[new]['seconds'])
            else:
                all_complete = False
                ratios.append(None)
        comparisons[name] = dict(
            numerator_arm=old, denominator_arm=new, paired_round_ratios=ratios,
            complete_pair_available_for_every_warmup_and_round=all_complete,
            paired_speed_comparison_supported=all_complete,
            median_paired_ratio=statistics.median(ratios) if all_complete else None,
            ratio_of_medians=(by_arm[old]['median_seconds']/by_arm[new]['median_seconds'])
            if all_complete else None)
    return dict(arms=by_arm, comparisons=comparisons)


def main_case(n, rounds, allowance):
    source = double_capped_fibonacci(n)
    raw, support = source['triangulation'], source['allowed_types']
    source_sha = _source_hash(raw)
    setup_started = time.perf_counter()
    shared = build_sector_kernel(raw, support)
    setup_seconds = time.perf_counter()-setup_started
    if len(shared.basis) != 3:
        raise AssertionError('double-capped source did not have matching nullity three')
    shared_sha = kernel_digest(shared)
    expected = [formula_rows(n, *parameters) for parameters in parameter_rays(n)]
    expected_sha = ray_digest(expected)
    arms = ('incumbent_full', 'planar_full', 'incumbent_postkernel', 'planar_postkernel')
    arguments = (raw, support, shared, allowance, None, expected, expected_sha, shared_sha, n)
    warmups = paired_round(arms, 0, True, *arguments)
    samples = [paired_round(arms, index, False, *arguments) for index in range(rounds)]
    if _source_hash(raw) != source_sha:
        raise AssertionError('source triangulation was mutated')
    return dict(case_id=f'double_capped_fibonacci_{n}', family='double_capped_fibonacci',
                base_tetrahedra=n, tetrahedra=n+2, source=source,
                source_sha256=source_sha, shared_kernel_sha256=shared_sha,
                shared_kernel_setup_seconds_outside_timing=setup_seconds,
                expected_rays=expected, expected_ray_sha256=expected_sha,
                expected_ray_count=7, matching_dimension=3,
                incumbent_arrangement_formulas=dict(
                    hyperplanes=2*n+6, positive_directions=(n+1)**2+3,
                    nonextreme_directions=(n-1)*(n+3), bases_attempted=comb(2*n+6, 2)),
                warmups=warmups, rounds=samples,
                summary=summaries(warmups, samples, {
                    'complete_construction_and_enumeration': ('incumbent_full', 'planar_full'),
                    'same_kernel_enumeration': ('incumbent_postkernel', 'planar_postkernel')}))


def control_case(n, rounds, allowance, prior):
    source = capped_fibonacci(n)
    raw, support = source['triangulation'], source['allowed_types']
    source_sha = _source_hash(raw)
    setup_started = time.perf_counter()
    shared = build_sector_kernel(raw, support)
    setup_seconds = time.perf_counter()-setup_started
    if len(shared.basis) != 2:
        raise AssertionError('one-cap source did not have matching nullity two')
    shared_sha = kernel_digest(shared)
    parameters = parameter_rays(n)
    expected = [formula_rows(n, *parameters[i])[:-1] for i in (0, 1, 4)]
    expected_sha = ray_digest(expected)
    arms = ('prior_envelope_postkernel', 'planar_postkernel')
    arguments = (raw, support, shared, allowance, prior, expected, expected_sha, shared_sha, None)
    warmups = paired_round(arms, 0, True, *arguments)
    samples = [paired_round(arms, index, False, *arguments) for index in range(rounds)]
    if _source_hash(raw) != source_sha:
        raise AssertionError('control source was mutated')
    return dict(case_id=f'prior_rank_two_control_{n}', family='capped_fibonacci',
                base_tetrahedra=n, tetrahedra=n+1, source=source,
                source_sha256=source_sha, shared_kernel_sha256=shared_sha,
                shared_kernel_setup_seconds_outside_timing=setup_seconds,
                expected_rays=expected, expected_ray_sha256=expected_sha,
                expected_ray_count=3, matching_dimension=2,
                warmups=warmups, rounds=samples,
                summary=summaries(warmups, samples, {
                    'prior_rank_two_incumbent_control': (
                        'prior_envelope_postkernel', 'planar_postkernel')}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prior-envelope', type=Path, required=True)
    parser.add_argument('--sizes', type=int, nargs='+', default=(1, 2, 4, 8, 16, 32))
    parser.add_argument('--control-sizes', type=int, nargs='+', default=(8, 32))
    parser.add_argument('--rounds', type=int, default=3)
    parser.add_argument('--allowance-seconds', type=float, default=40.0)
    args = parser.parse_args()
    if (args.rounds < 1 or args.allowance_seconds <= 0
            or any(size < 1 for size in list(args.sizes)+list(args.control_sizes))):
        parser.error('rounds, sizes, and allowance must be positive')
    fast = Path(__file__).resolve().parents[1]
    names = ('fastunknot/normal_sector.py', 'fastunknot/normal_surface_geometry.py',
             'fastunknot/sector_sparse.py', 'fastunknot/sector_planar.py',
             'planar_sector_research/fixtures.py', 'planar_sector_research/family_audit.py',
             'planar_sector_research/benchmark.py')
    source_pins = {name: sha256((fast/name).read_bytes()).hexdigest() for name in names}
    prior_sha = sha256(args.prior_envelope.read_bytes()).hexdigest()
    prior = load_prior(args.prior_envelope)
    results = dict(
        schema='planar-sector-paired-benchmark-v1',
        started_utc=datetime.now(timezone.utc).isoformat(),
        python=platform.python_version(), rounds=args.rounds,
        cooperative_arm_allowance_seconds=args.allowance_seconds,
        source_sha256=source_pins,
        prior_envelope=dict(path=str(args.prior_envelope.resolve()), sha256=prior_sha,
                            imported_name='fastunknot._prior_envelope', modified=False),
        timing_scope=(
            'Full arms include native geometry preparation, exact kernel construction, '
            'enumeration and every native coordinate validation performed by the lifts. '
            'Postkernel arms use the same immutable incumbent-built kernel. Fixture '
            'construction, setup of that shared kernel, hashes, exact comparison with '
            'the seven/three explicit formula rays, and serialization are untimed. '
            'No native component classification, coverage replay, sector search, or '
            'whole-knot recognition time is claimed.'),
        resource_semantics=(
            'A resource-limited arm retains its actual elapsed time, partial-output '
            'hash, count and statistics; its output is not a complete ray set. Any '
            'limited warmup or paired round suppresses that paired speed comparison. '
            'The allowance is cooperative and may be exceeded by one indivisible operation.'),
        main_cases=[], lower_dimension_controls=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)

    def checkpoint():
        results['last_checkpoint_utc'] = datetime.now(timezone.utc).isoformat()
        args.output.write_text(json.dumps(json_safe(results), indent=2, sort_keys=True)+'\n')

    for n in args.sizes:
        results['main_cases'].append(main_case(n, args.rounds, args.allowance_seconds))
        checkpoint()
    for n in args.control_sizes:
        results['lower_dimension_controls'].append(
            control_case(n, args.rounds, args.allowance_seconds, prior))
        checkpoint()
    if source_pins != {name: sha256((fast/name).read_bytes()).hexdigest() for name in names}:
        raise AssertionError('benchmark source changed during the run')
    if sha256(args.prior_envelope.read_bytes()).hexdigest() != prior_sha:
        raise AssertionError('prior envelope source changed during the run')
    results['status'] = 'COMPLETE'
    results['finished_utc'] = datetime.now(timezone.utc).isoformat()
    checkpoint()
    print('BENCHMARK COMPLETE', args.output, flush=True)


if __name__ == '__main__':
    main()
