"""Source-pinned Fitting, delivered primary, local-stop and corner comparisons.

Raw knot scans use a common prepared order; validation/order selection and
imports are excluded. Algebraic searches include the whole commutant solve,
candidate search and verified basis change. Compression includes recursive
splitting and sharing. Fresh fixture construction is excluded. The algebraic
fixtures are not claimed to arise from knot prefixes. No full-recognition
speedup is inferred. All arms use fresh state and exact uncapped computations.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
from time import perf_counter
import types

from fastunknot import Diagram, khovanov_rank
from fastunknot.ordering import best_scan_order
from fastunknot import scalar_split as current
from primary_research.families import two_field_scan
from benchmark_primary_split import probability_audit

ROOT = Path(__file__).resolve().parent
FITTING = '437b48c7f3a3d51c60ff4e4ee4a90bc53635d78b'
PRIMARY = '74446633a'
SEED = 26100879


def archive(commit, name):
    source = subprocess.check_output(['git', 'show', commit+
        ':Topology/UnknotRecognition/fast/fastunknot/scalar_split.py'], cwd=ROOT)
    module = types.ModuleType('fastunknot.'+name)
    exec(compile(source, '<'+commit+':scalar_split>', 'exec'), module.__dict__)
    return module, sha256(source).hexdigest()


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_hashes():
    names = ['fastunknot/scalar_split.py', 'fastunknot/primary_split.py',
             'fastunknot/corner_split.py', 'fastunknot/barcode_scan.py',
             'fastunknot/component_scan.py', 'fastunknot/recovered_grading.py',
             'primary_research/families.py', 'benchmark_primary_continuation.py',
             'benchmark_primary_split.py']
    return {name: sha256((ROOT/name).read_bytes()).hexdigest() for name in names}


def measure(factories, rounds, batches, rng):
    for factory in factories.values():
        factory()()  # One excluded warmup attempt per arm.
    samples, results = [], {}
    for _ in range(rounds):
        order = list(factories)
        rng.shuffle(order)
        times = {}
        for arm in order:
            calls = [factories[arm]() for _ in range(batches)]
            start = perf_counter()
            for call in calls:
                result = call()
            times[arm] = (perf_counter()-start)/batches
            results[arm] = result
        samples.append(dict(order=order, seconds_per_call=times))
    return dict(samples=samples, median_seconds={arm: median(s['seconds_per_call'][arm]
        for s in samples) for arm in factories}, median_paired_ratios={a+'/'+b:
        median(s['seconds_per_call'][a]/s['seconds_per_call'][b] for s in samples)
        for a,b in [('fitting','control'), ('fitting','primary'),
                    ('delivered','primary'), ('primary','corner')]}), results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--batches', type=int, default=2)
    args = parser.parse_args()
    if args.rounds < 1 or args.batches < 1:
        parser.error('positive rounds and batches required')
    old, old_hash = archive(FITTING, '_fitting_archive')
    delivered, delivered_hash = archive(PRIMARY, '_primary_archive')
    arms = dict(fitting=(old, {}), control=(old, {}),
        delivered=(delivered, dict(fitting_primary=True)),
        primary=(current, dict(fitting_primary=True)),
        corner=(current, dict(fitting_primary=True, fitting_reuse_commutant=True)))
    frozen, rng, knots, fields = source_hashes(), random.Random(SEED), [], []
    for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36', 'torus_3_5'):
        diagram = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
        order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
        reference = khovanov_rank(diagram.pd, order=order)
        def factory(module, options):
            def call():
                result = module.fitting_khovanov_rank(diagram.pd, order=order, **options)
                if result['by_degree'] != reference['by_degree']:
                    raise ArithmeticError('raw scan differs from ordinary Khovanov ranks')
                return dict(by_degree=result['by_degree'], stats=result['stats'])
            return lambda: call
        timing, results = measure({a: factory(*v) for a,v in arms.items()}, args.rounds, args.batches, rng)
        knots.append(dict(name=name, pd=diagram.pd, order=order,
                          reference_by_degree=reference['by_degree'], timing=timing, results=results))
        print(name, timing['median_seconds'], flush=True)
    for degree, mixing in [(r, 'dense') for r in (3,4,6,8,10,12)] + [(8,'bridge')]:
        seed = 2026100809  # Keep the delivered fixture/candidate comparison identical.
        initial, fixture = two_field_scan(degree, mixing=mixing, seed=seed)
        row = dict(degree=degree, mixing=mixing, fixture=fixture, original_entries=sum(map(len, initial.out)),
                   within_default_caps=degree<=10, objects=initial.live)
        for mode in ('search','compression'):
            def factory(module, options):
                def setup():
                    scan, _ = two_field_scan(degree, mixing=mixing, seed=seed,
                                             scan_class=module.FittingScan, **options)
                    def call():
                        if mode == 'search':
                            extra = dict(primary=True) if options else {}
                            rows, witness, metrics = module.find_scalar_split(scan, list(range(scan.live)),
                                max_variables=2*(2*degree)**2, **extra)
                            return dict(found=rows is not None, metrics=metrics,
                                transformed_sha256=digest(rows), witness_sha256=digest(witness))
                        scan._compress([0]*scan.live)
                        return dict(entries=sum(map(len,scan.out)), objects=scan.live,
                            templates=len(scan.weights), stats=scan.stats,
                            complex_sha256=digest((scan.mid,scan.deg,scan.out,scan.weights)))
                    return call
                return setup
            timing, results = measure({a: factory(*v) for a,v in arms.items()}, args.rounds, args.batches, rng)
            # Both optimizations retain the delivered primary split policy and
            # final exact representation; only proven futile trials are skipped.
            key = 'witness_sha256' if mode=='search' else 'complex_sha256'
            if len({results[a][key] for a in ('delivered','primary','corner')}) != 1:
                raise ArithmeticError('optimized primary path changed the split result')
            if results['fitting'] != results['control']:
                raise ArithmeticError('identical baseline arms disagree')
            row[mode] = dict(timing=timing, results=results)
        fields.append(row)
        print('field', degree,mixing,row['compression']['timing']['median_seconds'],flush=True)
    probabilities = probability_audit()
    assert source_hashes()==frozen, 'source changed during measurement'
    output = dict(scope=__doc__, python=platform.python_version(), platform=platform.platform(),
        seed=SEED, rounds=args.rounds,batches=args.batches,excluded_warmups_per_arm=1,
        source_sha256=frozen,source_hashes_unchanged=True,
        baseline_commits=dict(fitting=FITTING,delivered_primary=PRIMARY),
        archived_sha256=dict(fitting=old_hash,delivered_primary=delivered_hash),
        knots=knots,fields=fields,probabilities=probabilities)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2)+'\n')


if __name__ == '__main__':
    main()
