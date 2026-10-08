"""Paired commutant-inheritance and scalar-locality benchmarks.

Natural cases measure full raw Khovanov scans, including scanner construction,
at one common preselected order. They exclude input loading and order search.
Controlled cases measure recursive scalar compression and subsequent sharing;
fresh algebraic-fixture construction is outside the timed region. They are
honest homogeneous complexes, without a claimed realization as knot prefixes.
All arms have fresh states, randomized order, an untimed warm-up, and A/A
controls. Exact output comparisons and certificate audits are outside timing.
The historical arm loads only the pinned scalar_split.py against the same
maintained dependency modules, isolating that file's changes.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys
from time import perf_counter, process_time
from types import ModuleType

from fastunknot import Diagram, khovanov_rank
from fastunknot.ordering import best_scan_order
from fastunknot import scalar_split as current
from primary_research.families import two_field_scan

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tests'))
from test_scalar_split import mixed_copies

BASELINE = 'ea9cf443c8ce33e09ed0c48b0ef7856ddf6326a3'
SEED = 202610081745


def historical(path=None):
    if path is None:
        relative = 'Topology/UnknotRecognition/fast/fastunknot/scalar_split.py'
        source = subprocess.check_output(['git', 'show', f'{BASELINE}:{relative}'],
                                         text=True, cwd=ROOT)
        origin = f'{BASELINE}:{relative}'
    else:
        source, origin = path.read_text(), str(path)
    module = ModuleType('fastunknot._inheritance_baseline')
    module.__package__ = 'fastunknot'
    exec(compile(source, origin, 'exec'), module.__dict__)
    return module, dict(origin=origin, sha256=hashlib.sha256(source.encode()).hexdigest())


def source_hashes():
    names = ('fastunknot/scalar_split.py', 'fastunknot/primary_split.py',
             'primary_research/families.py', 'tests/test_scalar_inheritance.py',
             'benchmark_scalar_inheritance.py')
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in names}


def scan_summary(scan):
    signature = (scan.mid, scan.deg, scan.out, scan.weights)
    return signature, dict(objects=scan.live, components=len(scan.weights),
                           entries=sum(map(len, scan.out)), stats=scan.stats)


def rank_summary(result):
    return result['by_degree'], dict(rank=result['rank'], by_degree=result['by_degree'],
                                     stats=result['stats'])


def paired(makers, summarize, *, reference, rounds, batches, rng):
    samples, outcomes = [], {}
    expected = None
    for maker in makers.values():
        signature, _ = summarize(maker()())
        if expected is None:
            expected = signature
        elif signature != expected:
            raise ArithmeticError('warm-up arms disagree exactly')
    for _ in range(rounds):
        order = list(makers)
        rng.shuffle(order)
        wall, cpu = {}, {}
        for name in order:
            calls = [makers[name]() for _ in range(batches)]
            started, cpu_started = perf_counter(), process_time()
            for call in calls:
                result = call()
            wall[name] = (perf_counter() - started) / batches
            cpu[name] = (process_time() - cpu_started) / batches
            signature, outcomes[name] = summarize(result)
            if signature != expected:
                raise ArithmeticError(f'arm {name} differs from the exact reference')
        samples.append(dict(order=order, seconds_per_call=wall, cpu_seconds_per_call=cpu))
    return dict(samples=samples, batches=batches,
        median_seconds={name: statistics.median(s['seconds_per_call'][name] for s in samples)
                        for name in makers},
        median_reference_over={name: statistics.median(
            s['seconds_per_call'][reference] / s['seconds_per_call'][name] for s in samples)
            for name in makers if name != reference}, outcomes=outcomes)


def natural_cases(baseline, rounds, batches, rng):
    rows = []
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8',
                 'stress_braid5_36', 'torus_3_5'):
        diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
        order = best_scan_order(diagram.pd, tries=min(len(diagram.pd), 12))
        reference = khovanov_rank(diagram.pd, order=order)

        def maker(module, **options):
            def call():
                return module.fitting_khovanov_rank(diagram.pd, order=order, **options)
            return lambda: call

        makers = dict(baseline=maker(baseline), control=maker(baseline),
            inheritance=maker(current),
            primary=maker(current, fitting_primary=True, fitting_reuse_endomorphisms=False),
            locality=maker(current, fitting_primary=True, fitting_reuse_endomorphisms=False,
                           fitting_certify_local=True),
            monogenic=maker(current, fitting_primary=True, fitting_reuse_endomorphisms=True,
                            fitting_certify_local=True, fitting_monogenic_corners=True))
        measurement = paired(makers, rank_summary, reference='baseline', rounds=rounds,
                             batches=batches, rng=rng)
        if measurement['outcomes']['baseline']['by_degree'] != reference['by_degree']:
            raise ArithmeticError('Fitting and standard scanner ranks differ')
        rows.append(dict(name=name, crossings=len(diagram.pd), pd=diagram.pd, order=order,
                         reference_by_degree=reference['by_degree'], **measurement))
        print('natural', name, measurement['median_reference_over'], flush=True)
    return rows


def copy_cases(baseline, rounds, batches, rng):
    rows = []
    for copies in (4, 8, 12, 16, 24):
        def maker(scan_class, **options):
            def build():
                scan = mixed_copies(scan_class, copies, fitting_max_splits=32,
                    fitting_max_objects=3 * copies, fitting_max_variables=3 * copies * copies,
                    **options)
                def call():
                    scan._compress([0] * scan.live)
                    return scan
                return call
            return build
        measurement = paired(dict(baseline=maker(baseline.FittingScan),
            control=maker(baseline.FittingScan), inheritance=maker(current.FittingScan)),
            scan_summary, reference='baseline', rounds=rounds,
            batches=max(1, min(batches, 512 // (copies * copies))), rng=rng)
        rows.append(dict(copies=copies, objects=3 * copies, variables=3 * copies * copies,
                         within_default_caps=copies <= 16, **measurement))
        print('copies', copies, measurement['median_reference_over'], flush=True)
    return rows


def field_cases(rounds, batches, rng):
    rows = []
    for degree, mixing in [(r, 'dense') for r in (3, 6, 8, 10, 12)] + [(8, 'bridge')]:
        initial, evidence = two_field_scan(degree, mixing=mixing)
        def maker(**options):
            def build():
                scan, _ = two_field_scan(degree, mixing=mixing, fitting_primary=True, **options)
                def call():
                    scan._compress([0] * scan.live)
                    return scan
                return call
            return build
        makers = dict(primary=maker(fitting_reuse_endomorphisms=False),
            control=maker(fitting_reuse_endomorphisms=False),
            inheritance=maker(fitting_reuse_endomorphisms=True),
            locality=maker(fitting_reuse_endomorphisms=False, fitting_certify_local=True),
            combined=maker(fitting_reuse_endomorphisms=True, fitting_certify_local=True),
            monogenic=maker(fitting_reuse_endomorphisms=True, fitting_certify_local=True,
                            fitting_monogenic_corners=True))
        measurement = paired(makers, scan_summary, reference='primary', rounds=rounds,
                             batches=max(1, min(batches, 256 // (degree * degree))), rng=rng)
        rows.append(dict(degree=degree, mixing=mixing, fixture=evidence,
                         objects=initial.live, variables=8 * degree * degree,
                         within_default_caps=degree <= 10, **measurement))
        print('fields', degree, mixing, measurement['median_reference_over'], flush=True)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--baseline-file', type=Path)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--batches', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1 or args.batches < 1:
        parser.error('rounds and batches must be positive')
    baseline, provenance = historical(args.baseline_file)
    hashes, rng = source_hashes(), random.Random(SEED)
    result = dict(schema='scalar-corner-inheritance-v1', scope=__doc__,
        python=platform.python_version(), platform=platform.platform(), seed=SEED,
        baseline=provenance, source_hashes=hashes, rounds=args.rounds,
        requested_batches=args.batches,
        natural=natural_cases(baseline, args.rounds, args.batches, rng),
        copies=copy_cases(baseline, args.rounds, args.batches, rng),
        fields=field_cases(args.rounds, args.batches, rng))
    if hashes != source_hashes():
        raise ArithmeticError('benchmark source changed while measurements were running')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
