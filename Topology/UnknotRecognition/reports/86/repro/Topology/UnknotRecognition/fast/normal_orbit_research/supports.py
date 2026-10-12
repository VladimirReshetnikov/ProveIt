"""Pinned complete orbit and native-recognition evidence for support pruning."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '7b0746a27526fd4cd46f9aec0a9f9bdd9fd3ebd5'
SOURCE_AUDIT = ROOT.parent/'synthesis/data/cocycle-seed-audit.json'
PREVIOUS = ROOT.parent/'synthesis/data/cocycle-sparse-audit.json'


def baseline():
    path = 'Topology/UnknotRecognition/fast/fastunknot/interval_orbits.py'
    source = subprocess.check_output(['git', 'show', BASELINE+':'+path], cwd=ROOT)
    module = ModuleType('_support_baseline')
    module.__package__ = 'fastunknot'
    sys.modules[module.__name__] = module
    exec(compile(source, BASELINE+':'+path, 'exec'), module.__dict__)
    # Both versions accept the same immutable public pairing values.
    module.IntervalPairing = IntervalPairing
    return module.count_orbits, sha256(source).hexdigest()


def pins():
    result = seeds.sources()
    for p in (SOURCE_AUDIT, PREVIOUS):
        result[str(p.relative_to(ROOT.parent))] = sha256(p.read_bytes()).hexdigest()
    return result


def random_system(rng):
    size = rng.randrange(1, 50)
    pairs = []
    for _ in range(rng.randrange(0, 30)):
        width = rng.randrange(1, size+1)
        a, c = (rng.randrange(size-width+1) for _ in range(2))
        pairs.append(IntervalPairing(a, a+width-1, c, c+width-1, bool(rng.getrandbits(1))))
    return size, pairs


def audit(old):
    rng = random.Random(261009467)
    comparisons = []
    for trial in range(300):
        n, pairs = random_system(rng)
        for rule in ('fine_wilf', 'aht'):
            before = old(n, pairs, periodic_rule=rule, record_certificate=True)
            after = count_orbits(n, pairs, periodic_rule=rule, record_certificate=True)
            assert before.certificate == after.certificate
            assert before.orbits == after.orbits and before.cycles == after.cycles
            assert verify_orbit_certificate(n, pairs, after.certificate)
            comparisons.append(dict(trial=trial, rule=rule, cycles=after.cycles,
                old_stats=before.stats, new_stats=after.stats, certificate_sha256=seeds.digest(after.certificate)))
    inputs = json.loads(SOURCE_AUDIT.read_text())['cases']
    previous = {r['name']: r['result'] for r in json.loads(PREVIOUS.read_text())['cases']}
    records = []
    for entry in inputs:
        source = entry['source']; diagram = Diagram.from_pd(source['pd'])
        answer = normal_seed_decide(diagram)
        if answer['status'] == 'UNKNOT':
            assert source['expected'] == 'UNKNOT'
            assert verify_normal_seed_certificate(diagram, answer['certificate'])
            answer['certificate_sha256'] = seeds.digest(answer.pop('certificate'))
            if entry['result']['status'] == 'UNKNOT':
                assert answer['certificate_sha256'] == entry['result']['certificate_sha256']
        if previous[source['name']]['status'] == 'UNKNOT':
            assert answer['status'] == 'UNKNOT'
        records.append(dict(name=source['name'], old=previous[source['name']], result=answer))
        print(source['name'], answer['status'], answer['work'], flush=True)
    return dict(orbit_comparisons=comparisons, source_cases=records,
                source_replays=sum(r['result']['status'] == 'UNKNOT' for r in records))


def benchmark(old, mode, rounds):
    if mode == 'orbits':
        cases = [(f'disjoint-{k}', (2*k, [IntervalPairing(2*i, 2*i, 2*i+1, 2*i+1)
                                        for i in range(k)])) for k in (16, 64, 256)]
        for k, bits in ((16, 0), (16, 4096)):
            scale = 10*k+(1 << bits)
            pairs = [IntervalPairing(i, scale+2*i-1, scale+2*i, 2*scale+3*i-1)
                     for i in range(k+1)]
            cases.append((f'five-cycle-{k}-bits-{bits}', (2*scale+3*k, pairs[:-1]+[pairs[-1]]*k)))
        def run(case, use_old):
            n, pairs = case
            result = (old if use_old else count_orbits)(n, pairs, record_certificate=True)
            assert result.complete and verify_orbit_certificate(n, pairs, result.certificate)
            return dict(completed=True, orbits=result.orbits, cycles=result.cycles,
                        stats=result.stats, certificate_sha256=seeds.digest(result.certificate))
    else:
        cases = [(f'circle-{n}', Diagram.from_braid(n+1, list(range(1, n+1))).pd) for n in (8, 16, 32)]
        cases += [('optimized-positive', Diagram.from_braid(4, [-1, 2, 1, -2, 3]).pd),
                  ('trefoil', Diagram.from_braid(2, [1, 1, 1]).pd)]
        def run(pd, use_old):
            with patch('fastunknot.weighted_orbits.count_orbits', old if use_old else count_orbits):
                result = recognize(Diagram.from_pd(pd), **seeds.FORCED)
            assert result.status == ('KNOTTED' if pd == cases[-1][1] else 'UNKNOT')
            native = result.evidence['normal_seed']
            return dict(completed=True, status=result.status, method=result.method,
                        native_status=native['status'], native_work=native['work'],
                        certificate_sha256=seeds.digest(native['certificate']) if 'certificate' in native else None)
    return seeds.rounds(cases, run, rounds)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'orbits', 'recognize'))
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old, old_hash = baseline()
    before = pins(); start = time.perf_counter()
    result = audit(old) if args.mode == 'audit' else benchmark(old, args.mode, args.rounds)
    elapsed = time.perf_counter()-start
    assert pins() == before
    result.update(mode=args.mode, source_sha256=before, baseline_commit=BASELINE,
                  baseline_module_sha256=old_hash, elapsed_seconds=elapsed,
                  python=platform.python_version(), platform=platform.platform(), seed=261009467)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(args.mode, 'complete', elapsed, flush=True)


if __name__ == '__main__':
    main()
