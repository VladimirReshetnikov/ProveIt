"""Paired signed-Tait block timings with separate actual observer traces.

Fresh diagram construction and setup are timed in every sample. Primitive
closure, complete raw shadow scan, and complete recognition are distinct scopes.
Traces are collected outside timings and include only actual driver requests.
Imports and one warmup per arm are excluded; UNKNOWN suppresses all case ratios.
"""
import argparse
from collections import Counter
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


def load_baseline():
    revision = subprocess.check_output(['git', 'rev-parse', '2c7c8df3f^{commit}'], cwd=HERE, text=True).strip()
    source = subprocess.check_output(['git', 'show', revision +
        ':Topology/UnknotRecognition/fast/fastunknot/shadow_scan.py'], cwd=HERE, text=True)
    old = ModuleType('fastunknot._tait_block_baseline')
    old.__package__ = 'fastunknot'
    exec(compile(source, revision + ':shadow_scan.py', 'exec'), old.__dict__)
    return revision, old


def trace_driver(module, data):
    original = module.ClosureShadow
    instances = []
    class Trace(original):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.queries, self.ones = Counter(), Counter()
            instances.append(self)
        def evaluate(self, stage, pairs):
            if (stage, tuple(pairs)) not in self.shadow_cache:
                self.queries[stage] += 1
            return super().evaluate(stage, pairs)
        def evaluate_one(self, stage, pairs):
            if (stage, tuple(pairs)) not in self.cache:
                self.ones[stage] += 1
            return super().evaluate_one(stage, pairs)
    module.ClosureShadow = Trace
    try:
        d = Diagram.from_json(data)
        out = module.shadow_compressed_khovanov_decide(d.pd, max_objects=50000, seconds=5)
        status = {k: out[k] for k in ('status', 'method', 'stage', 'shadow_exhausted')}
    except (ScanLimit, MemoryError) as exc:
        status = dict(status='UNKNOWN', reason=str(exc))
    finally:
        module.ClosureShadow = original
    engine = instances[-1]
    return dict(**status, new_shadow_queries=dict(engine.queries), new_euler_queries=dict(engine.ones),
                stats=engine.stats)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    revision, old = load_baseline()
    rng, rows, traces = random.Random(2612), [], []
    for path in sorted((HERE/'examples').glob('*.json')):
        data = json.loads(path.read_text())
        n = Diagram.from_json(data).crossings
        traces.append(dict(name=path.stem, crossings=n, baseline=trace_driver(old, data),
                           current=trace_driver(shadow_scan, data)))
        for scope in ('closure', 'raw-shadow', 'recognition-shadow'):
            if not n and scope == 'closure':
                continue
            def run(arm):
                module = shadow_scan if arm == 'blocks' else old
                d = Diagram.from_json(data)
                try:
                    if scope == 'closure':
                        engine = module.ClosureShadow(d.pd, list(range(n)), max_work=None)
                        value = engine.evaluate(0, ())
                        return value, dict(value=value, stats=engine.stats)
                    if scope == 'raw-shadow':
                        out = module.shadow_compressed_khovanov_decide(d.pd, max_objects=50000, seconds=5)
                        return (out['status'], out['method'], out['stage']), {
                            k: out[k] for k in ('status', 'method', 'stage', 'shadow_exhausted', 'shadow_stats')}
                    saved = shadow_scan.shadow_compressed_khovanov_decide
                    try:
                        shadow_scan.shadow_compressed_khovanov_decide = module.shadow_compressed_khovanov_decide
                        out = recognize(d, backend='shadow', seconds=5, max_objects=50000)
                    finally:
                        shadow_scan.shadow_compressed_khovanov_decide = saved
                    if out.status == 'UNKNOWN':
                        return 'UNKNOWN', dict(status=out.status, method=out.method)
                    return (out.status, out.method), dict(status=out.status, method=out.method)
                except (ScanLimit, MemoryError) as exc:
                    return 'UNKNOWN', dict(reason=str(exc))
            arms = ('direct', 'control', 'blocks')
            warm = []
            for arm in arms:
                start = perf_counter()
                run(arm)
                warm.append(perf_counter()-start)
            repetitions = max(1, min(40, int(.01/max(warm))))
            samples, evidence, expected = [], {}, None
            for _ in range(7):
                order = list(arms)
                rng.shuffle(order)
                times, statuses = {}, {}
                for arm in order:
                    start = perf_counter()
                    results = [run(arm) for _ in range(repetitions)]
                    times[arm] = (perf_counter()-start)/repetitions
                    statuses[arm] = 'complete'
                    for signature, detail in results:
                        if signature == 'UNKNOWN':
                            statuses[arm] = 'UNKNOWN'
                            continue
                        if expected is None:
                            expected = signature
                        assert signature == expected, (path.stem, scope, arm, signature, expected)
                    evidence[arm] = results[-1][1]
                samples.append(dict(order=order, seconds=times, statuses=statuses))
            complete = all(all(v == 'complete' for v in s['statuses'].values()) for s in samples)
            ratios = {a: statistics.median(s['seconds']['direct']/s['seconds'][a] for s in samples)
                      for a in arms[1:]} if complete else None
            rows.append(dict(name=path.stem, crossings=n, input=data, scope=scope,
                             repetitions=repetitions, samples=samples, evidence=evidence,
                             complete=complete, median_speedups=ratios))
            print(scope, path.stem, {k: round(v, 3) for k, v in (ratios or {}).items()}, flush=True)
    paths = [Path(__file__)] + [HERE/'fastunknot'/name for name in
        ('shadow_scan.py', 'tait_blocks.py', 'euler_scan.py', 'recognize.py', 'ordering.py')]
    output = dict(scope=__doc__, baseline_revision=revision, baseline_scope='shadow_scan.py only; other dependencies shared',
                  rounds=7, seed=2612, python=platform.python_version(), traces=traces, rows=rows,
                  sources={str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
