"""Certify conservation shortcuts against the published weighted replay."""
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
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds, supports

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '8160ec4480f76ec85ab6149b9ef86a4a6e791dfa'
SOURCE = ROOT.parent/'synthesis/data/cocycle-seed-audit.json'
PREVIOUS = ROOT.parent/'synthesis/data/orbit-support-audit.json'


def baseline():
    modules, hashes = [], {}
    for name in ('weighted_orbits', 'weighted_orbit_verify'):
        path = 'Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        source = subprocess.check_output(['git', 'show', BASELINE+':'+path], cwd=ROOT)
        module = ModuleType('_single_orbit_baseline_'+name)
        module.__package__ = 'fastunknot'
        sys.modules[module.__name__] = module
        exec(compile(source, BASELINE+':'+path, 'exec'), module.__dict__)
        modules.append(module); hashes[name] = sha256(source).hexdigest()
    return modules, hashes


def pins():
    result = seeds.sources()
    for path in (SOURCE, PREVIOUS):
        result[str(path.relative_to(ROOT.parent))] = sha256(path.read_bytes()).hexdigest()
    return result


def audit(old, old_verify):
    rng = random.Random(261009469)
    records = []
    for trial in range(300):
        size, pairs = supports.random_system(rng)
        dimension = rng.randrange(1, 8)
        weights = []
        for _ in range(rng.randrange(0, 15)):
            lo = rng.randrange(size+1); hi = rng.randrange(lo, size+1)
            weights.append((lo, hi, [rng.randrange(-10, 11) for _ in range(dimension)]))
        before = old(size, pairs, weights, dimension=dimension, record_certificate=True)
        after = weighted_orbit_histogram(size, pairs, weights, dimension=dimension, record_certificate=True)
        assert before['certificate'] == after['certificate']
        assert old_verify(size, pairs, weights, after['certificate'], dimension=dimension)
        assert verify_weighted_orbit_certificate(size, pairs, weights, before['certificate'], dimension=dimension)
        records.append(dict(size=size, dimension=dimension, orbits=after['orbit_count'],
                            old_stats=before['stats'], new_stats=after['stats'],
                            certificate_sha256=seeds.digest(after['certificate'])))
    previous = {r['name']: r['result'] for r in json.loads(PREVIOUS.read_text())['source_cases']}
    cases, proofs = [], {}
    for entry in json.loads(SOURCE.read_text())['cases']:
        source = entry['source']; diagram = Diagram.from_pd(source['pd'])
        answer = normal_seed_decide(diagram)
        if answer['status'] == 'UNKNOT':
            assert source['expected'] == 'UNKNOT'
            assert verify_normal_seed_certificate(diagram, answer['certificate'])
            key = seeds.digest(answer['certificate'])
            if entry['result']['status'] == 'UNKNOT':
                assert key == entry['result']['certificate_sha256']
            else:
                proofs[key] = answer['certificate']
            answer.pop('certificate'); answer['certificate_sha256'] = key
        if previous[source['name']]['status'] == 'UNKNOT':
            assert answer['status'] == 'UNKNOT'
        cases.append(dict(name=source['name'], old_status=previous[source['name']]['status'],
                          old_work=previous[source['name']]['work'], result=answer))
        print(source['name'], answer['status'], answer['work'], flush=True)
    return dict(weighted_comparisons=records, source_cases=cases, new_source_proofs=proofs,
                source_replays=sum(r['result']['status'] == 'UNKNOT' for r in cases))


def benchmark(old, old_verify, mode, rounds):
    if mode == 'weighted':
        cases = [('connected-3', (3, 0)), ('connected-128', (128, 0)),
                 ('connected-128-binary', (128, 4096)), ('disconnected-control', (3, -1))]
        def run(case, use_old):
            dimension, bits = case
            if bits == -1:
                n, pairs = 256, [IntervalPairing(0, 255, 0, 255, True)]
            else:
                m, scale = 16, 160+(1 << bits)
                initial = [IntervalPairing(i, scale+2*i-1, scale+2*i, 2*scale+3*i-1) for i in range(m+1)]
                n, pairs = 2*scale+3*m, initial[:-1]+[initial[-1]]*m
            weights = [(n*i//32, n*(i+1)//32, [((i+1)*(j+3)) % 13-6 for j in range(dimension)])
                       for i in range(32)]
            producer = old if use_old else weighted_orbit_histogram
            verifier = old_verify if use_old else verify_weighted_orbit_certificate
            result = producer(n, pairs, weights, record_certificate=True)
            assert verifier(n, pairs, weights, result['certificate'])
            return dict(completed=True, orbits=result['orbit_count'], stats=result['stats'],
                        certificate_sha256=seeds.digest(result['certificate']))
    else:
        cases = [(f'circle-{n}', Diagram.from_braid(n+1, list(range(1, n+1))).pd) for n in (8, 16, 32)]
        cases += [('optimized-positive', Diagram.from_braid(4, [-1, 2, 1, -2, 3]).pd),
                  ('trefoil', Diagram.from_braid(2, [1, 1, 1]).pd)]
        def run(pd, use_old):
            producer = old if use_old else weighted_orbit_histogram
            verifier = old_verify if use_old else verify_weighted_orbit_certificate
            with patch('fastunknot.normal_surface_components.weighted_orbit_histogram', producer), \
                 patch('fastunknot.normal_component_verify.verify_weighted_orbit_certificate', verifier):
                result = recognize(Diagram.from_pd(pd), **seeds.FORCED)
            assert result.status == ('KNOTTED' if pd == cases[-1][1] else 'UNKNOT')
            native = result.evidence['normal_seed']
            return dict(completed=True, status=result.status, method=result.method,
                        native_status=native['status'], native_work=native['work'],
                        certificate_sha256=seeds.digest(native['certificate']) if 'certificate' in native else None)
    return seeds.rounds(cases, run, rounds)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'weighted', 'recognize'))
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    modules, hashes = baseline()
    old, old_verify = modules[0].weighted_orbit_histogram, modules[1].verify_weighted_orbit_certificate
    before = pins(); start = time.perf_counter()
    result = audit(old, old_verify) if args.mode == 'audit' else benchmark(old, old_verify, args.mode, args.rounds)
    elapsed = time.perf_counter()-start
    assert pins() == before
    result.update(mode=args.mode, source_sha256=before, baseline_commit=BASELINE,
                  baseline_module_sha256=hashes, elapsed_seconds=elapsed,
                  python=platform.python_version(), platform=platform.platform(), seed=261009469)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(args.mode, 'complete', elapsed, flush=True)


if __name__ == '__main__':
    main()
