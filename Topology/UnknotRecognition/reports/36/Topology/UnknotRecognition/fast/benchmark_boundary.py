"""Separate boundary-oracle batches, complete raw scans, and recognition.

Every sample includes fresh engine setup. Actual matching streams come from a
validated production prefix, with cancelling braid pairs lengthening its suffix.
These deliberately isolate reuse; they are not a hard recognition family.
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
from time import perf_counter
from types import ModuleType

from fastunknot import Diagram, recognize, euler_scan
from fastunknot.euler_scan import AdaptiveClosureEuler, ClosureEuler
from fastunknot.geometry import ScanLimit
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import ClosureShadow

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'determinant_research'))
from boundary_tait import BoundaryTait

WORD = [-2, 3, 2, 2, 4, 2, -3, -2, -1, 1, -2, -1, -2, -2]
ORDER = [5, 1, 10, 2, 9, 11, 13, 6, 7, 0, 12, 4, 8, 3]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    revision = subprocess.check_output(['git', 'rev-parse', 'f0179ab50^{commit}'], text=True).strip()
    source = subprocess.check_output(['git', 'show', revision+
        ':Topology/UnknotRecognition/fast/fastunknot/euler_scan.py'], text=True)
    old = ModuleType('fastunknot._boundary_baseline')
    old.__package__ = 'fastunknot'
    exec(compile(source, revision+':euler_scan.py', 'exec'), old.__dict__)
    current = euler_scan.euler_compressed_khovanov_decide
    rng = random.Random(2609)
    rows = []

    def measure(name, scope, arms, run, input_data, batch=False):
        warm = []
        for arm in arms:
            start = perf_counter()
            run(arm)
            warm.append(perf_counter()-start)
        repetitions = 1 if batch else max(1, min(30, int(.005/max(warm))))
        samples, evidence = [], {}
        expected = None
        for _ in range(7):
            order = list(arms)
            rng.shuffle(order)
            times, statuses = {}, {}
            for arm in order:
                results = []
                start = perf_counter()
                for _ in range(repetitions):
                    results.append(run(arm))
                times[arm] = (perf_counter()-start)/repetitions
                statuses[arm] = 'complete'
                for signature, detail in results:
                    if signature == 'UNKNOWN':
                        statuses[arm] = 'UNKNOWN'
                        continue
                    if expected is None:
                        expected = signature
                    assert signature == expected, (name, scope, arm)
                evidence[arm] = results[-1][1]
            samples.append(dict(order=order, seconds=times, statuses=statuses))
        complete = all(all(v == 'complete' for v in s['statuses'].values()) for s in samples)
        ratios = {a: statistics.median(s['seconds'][arms[0]]/s['seconds'][a] for s in samples)
                  for a in arms[1:]} if complete else None
        rows.append(dict(name=name, scope=scope, input=input_data, repetitions=repetitions,
                         samples=samples, evidence=evidence, complete=complete, median_speedups=ratios))
        print(scope, name, {k: round(v, 3) for k, v in (ratios or {}).items()}, flush=True)

    for extra in (0, 16, 64, 256):
        word = WORD+[1, -1]*extra
        d = Diagram.from_braid(5, word)
        order = ORDER+list(range(len(WORD), d.crossings))
        scan = FastScan(shape_cache=False)
        for i in order[:9]:
            scan.add_crossing(d.pd[i])
        pairs = [scan.algebra.pairs[m] for m in sorted(set(scan.mid)-{None})]
        input_data = dict(strands=5, word=word, order=order, stage=9, pairs=pairs,
                          suffix_crossings=d.crossings-9, frontier=len(scan.points))

        def euler_batch(arm):
            engine = (ClosureEuler(d.pd, order, max_states=None) if arm in ('direct', 'control')
                      else AdaptiveClosureEuler(d.pd, order, max_states=None,
                                               compression_after=0 if arm == 'eager' else 4))
            return tuple(engine.evaluate(9, p) for p in pairs), dict(engine.stats)

        measure('suffix_'+str(d.crossings-9), 'euler-stream',
                ['direct', 'control', 'adaptive', 'eager'], euler_batch, input_data, True)

        def shadow_batch(arm):
            if arm in ('direct', 'control'):
                engine = ClosureShadow(d.pd, order, max_states=None, max_work=None)
                return tuple(engine.evaluate(9, p) for p in pairs), dict(engine.stats)
            engine = BoundaryTait(d.pd, order, 9)
            vectors = []
            for p in pairs:
                z, data = engine.evaluate(p)
                parity = (data['zero_circles']-1) % 2
                assert z[1-parity] == 0
                a, difference = data['unreduced_euler']//2, z[parity]
                assert (a+difference) % 2 == 0
                v = [0]*4
                v[parity], v[parity+2] = (a+difference)//2, (a-difference)//2
                vectors.append(tuple(v))
            return tuple(vectors), dict(vertices=len(engine.laplacian), terminals=len(engine.terminals),
                                        nullity=engine.kernel.nullity if engine.kernel else None,
                                        distinct_determinants=len(engine.cache))

        measure('suffix_'+str(d.crossings-9), 'shadow-stream',
                ['direct', 'control', 'boundary'], shadow_batch, input_data, True)

    for name in ('conway', 'kinoshita_terasaka', 'conway_sum_2', 'conway_sum_8',
                 'hard_unknot_8', 'grid_scrambled_unknot', 'stress_braid5_36'):
        data = json.loads((HERE/'examples'/(name+'.json')).read_text())
        for scope in ('raw-euler', 'recognition-euler'):
            def run(arm):
                d = Diagram.from_json(data)
                decide = current if arm == 'adaptive' else old.euler_compressed_khovanov_decide
                try:
                    if scope == 'raw-euler':
                        out = decide(d.pd, max_objects=50000, seconds=5)
                        return (out['status'], out['method'], out['stage']), dict(
                            status=out['status'], method=out['method'], stage=out['stage'],
                            euler_stats=out['euler_stats'])
                    # Apply the same dispatch instrumentation to every arm;
                    # the current recognizer and all earlier filters are shared.
                    saved = euler_scan.euler_compressed_khovanov_decide
                    try:
                        euler_scan.euler_compressed_khovanov_decide = decide
                        out = recognize(d, backend='euler', max_objects=50000, seconds=5)
                    finally:
                        euler_scan.euler_compressed_khovanov_decide = saved
                    if out.status == 'UNKNOWN':
                        return 'UNKNOWN', dict(status=out.status, method=out.method)
                    return (out.status, out.method), dict(status=out.status, method=out.method)
                except (ScanLimit, MemoryError) as exc:
                    return 'UNKNOWN', dict(reason=str(exc))
            measure(name, scope, ['direct', 'control', 'adaptive'], run, data)

    files = [Path(__file__), HERE/'fastunknot/euler_scan.py', HERE/'fastunknot/boundary_connectivity.py',
             HERE/'fastunknot/shadow_scan.py', HERE/'determinant_research/boundary_tait.py',
             HERE.parent/'reports/26/detshadow/linalg.py', HERE.parent/'reports/26/detshadow/diagram.py']
    output = dict(scope=__doc__, seed=2609, rounds=7, python=platform.python_version(),
                  baseline_revision=revision, baseline_scope='euler_scan.py only; recognition and other dependencies shared',
                  kernel_verification='Independent certificate audit is outside timed calls; kernel construction is inside',
                  rows=rows, sources={str(p.relative_to(HERE.parent)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
