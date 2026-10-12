"""Paired fallback scheduling with a fixed shared Euler query allowance.

Compare the previous stop-all-observations policy with shadow-to-Euler fallback.
Raw shadow scans and complete recognition are timed separately, including fresh
input construction and all setup. Explicit-order cases are raw-only. There are
seven shuffled paired rounds, an identical baseline control, and one excluded
warmup. All successful arms must agree on verdict; methods and stages may differ.
UNKNOWN suppresses all timing ratios for that case and scope.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

from fastunknot import Diagram, recognize, shadow_scan
from fastunknot.geometry import ScanLimit

HERE = Path(__file__).resolve().parent


def cases():
    for path in sorted((HERE/'examples').glob('*.json')):
        yield path.stem, json.loads(path.read_text()), 1_000_000, 4096, None
    for name, work, states in [('conway_sum_8', 0, 4096), ('conway_sum_8', 2800, 4096),
                                ('conway_sum_8', 2800, 1), ('torus_3_5', 0, 4096),
                                ('hard_unknot_8', 0, 4096)]:
        data = json.loads((HERE/'examples'/(name+'.json')).read_text())
        yield f'{name}_w{work}_q{states}', data, work, states, None
    parts = [Diagram.from_json(json.loads((HERE/'examples/conway.json').read_text())),
             Diagram.from_braid(3, [1, 2]*151)]
    rows = [[-1]*4 for _ in range(sum(d.crossings for d in parts))]
    position = offset = 0
    for diagram in parts:
        for dart in diagram.traversal():
            crossing, slot = divmod(dart, 4)
            rows[offset+crossing][slot] = position
            rows[offset+crossing][(slot+2) % 4] = (position+1) % (2*len(rows))
            position += 1
        offset += diagram.crossings
    diagram = Diagram.from_pd(rows)
    data = dict(pd=diagram.pd)
    yield 'conway_torus151_heuristic', data, 1_000_000, 4096, None
    yield 'conway_torus151_supplied', data, 1_000_000, 4096, list(range(diagram.crossings))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    revision = subprocess.check_output(['git', 'rev-parse', '82fdfe15b^{commit}'], cwd=HERE, text=True).strip()
    source = subprocess.check_output(['git', 'show', revision+
        ':Topology/UnknotRecognition/fast/fastunknot/shadow_scan.py'], cwd=HERE, text=True)
    old = ModuleType('fastunknot._shadow_fallback_baseline')
    old.__package__ = 'fastunknot'
    exec(compile(source, revision+':shadow_scan.py', 'exec'), old.__dict__)
    rng, rows = random.Random(2614), []
    for name, data, work, states, crossing_order in cases():
        options = dict(shadow_max_work=work, euler_max_states=states)
        scopes = ('raw-shadow',) if crossing_order is not None else ('raw-shadow', 'recognition-shadow')
        for scope in scopes:
            def run(arm):
                module = shadow_scan if arm == 'fallback' else old
                d = Diagram.from_json(data)
                try:
                    if scope == 'raw-shadow':
                        out = module.shadow_compressed_khovanov_decide(d.pd, order=crossing_order,
                            max_objects=50000, seconds=5, **options)
                        evidence = {k: out[k] for k in ('status', 'method', 'stage', 'order',
                                    'shadow_exhausted', 'shadow_stats')}
                        evidence['euler_exhausted'] = out.get('euler_exhausted')
                        return out['status'], evidence
                    saved = shadow_scan.shadow_compressed_khovanov_decide
                    try:
                        shadow_scan.shadow_compressed_khovanov_decide = module.shadow_compressed_khovanov_decide
                        out = recognize(d, backend='shadow', seconds=5, max_objects=50000, **options)
                    finally:
                        shadow_scan.shadow_compressed_khovanov_decide = saved
                    return out.status, dict(status=out.status, method=out.method)
                except (ScanLimit, MemoryError) as exc:
                    return 'UNKNOWN', dict(reason=str(exc))
            arms = ('baseline', 'control', 'fallback')
            warm = []
            for arm in arms:
                start = perf_counter()
                run(arm)
                warm.append(perf_counter()-start)
            repetitions = max(1, min(40, int(.01/max(warm))))
            samples, evidence, expected = [], {}, None
            for _ in range(7):
                execution_order = list(arms)
                rng.shuffle(execution_order)
                times, statuses = {}, {}
                for arm in execution_order:
                    start = perf_counter()
                    results = [run(arm) for _ in range(repetitions)]
                    times[arm] = (perf_counter()-start)/repetitions
                    statuses[arm] = 'complete'
                    for signature, _ in results:
                        if signature == 'UNKNOWN':
                            statuses[arm] = 'UNKNOWN'
                            continue
                        if expected is None:
                            expected = signature
                        assert signature == expected, (name, scope, arm, signature, expected)
                    evidence[arm] = results[-1][1]
                samples.append(dict(order=execution_order, seconds=times, statuses=statuses))
            complete = all(all(v == 'complete' for v in s['statuses'].values()) for s in samples)
            ratios = {a: statistics.median(s['seconds']['baseline']/s['seconds'][a] for s in samples)
                      for a in arms[1:]} if complete else None
            rows.append(dict(name=name, input=data, options=options, crossing_order=crossing_order,
                             scope=scope, repetitions=repetitions, samples=samples, evidence=evidence,
                             complete=complete, median_speedups=ratios))
            print(scope, name, {k: round(v, 3) for k,v in (ratios or {}).items()},
                  {k:(v.get('status','UNKNOWN'), v.get('method'), v.get('stage')) for k,v in evidence.items()}, flush=True)
    paths = [Path(__file__)] + [HERE/'fastunknot'/name for name in
        ('shadow_scan.py', 'tait_blocks.py', 'euler_scan.py', 'recognize.py', 'ordering.py')]
    output = dict(scope=__doc__, baseline_revision=revision,
                  baseline_scope='shadow_scan.py only; other dependencies shared',
                  rounds=7, seed=2614, python=platform.python_version(), rows=rows,
                  sources={str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
