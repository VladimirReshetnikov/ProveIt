"""Certified span optima and source recognition with adaptive blocking flow."""
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
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation, regina_surface
from primitive_power_research import forests

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '4fa723b7982202af6e25d486c9a0573a409c1132'
SOURCE = ROOT.parent/'synthesis/data/cocycle-seed-audit.json'
PREVIOUS = ROOT.parent/'synthesis/data/cocycle-trees-audit.json'


def baseline():
    path = 'Topology/UnknotRecognition/fast/fastunknot/cocycle_span.py'
    source = subprocess.check_output(['git', 'show', BASELINE+':'+path], cwd=ROOT)
    module = ModuleType('_cocycle_blocking_baseline')
    module.__package__ = 'fastunknot'
    sys.modules[module.__name__] = module
    exec(compile(source, BASELINE+':'+path, 'exec'), module.__dict__)
    return module.minimize_cocycle_span, sha256(source).hexdigest()


def pins():
    result = seeds.sources()
    for path in (SOURCE, PREVIOUS):
        result[str(path.relative_to(ROOT.parent))] = sha256(path.read_bytes()).hexdigest()
    return result


def compact(result):
    return dict(stats=result['stats'], certificate_sha256=seeds.digest(result['certificate']),
                coordinates_sha256=seeds.digest(result['coordinates']))


def audit(old):
    rng = random.Random(261009475)
    comparisons = []
    for trial in range(500):
        n, k = rng.randrange(1, 31), rng.randrange(1, 13)
        vertices = [[rng.randrange(k) for _ in range(4)] for _ in range(n)]
        heights = [[rng.randrange(-100, 101) for _ in range(4)] for _ in range(n)]
        if trial == 499: heights = [[h*(1 << 20000) for h in row] for row in heights]
        before, after = old(vertices, heights), minimize_cocycle_span(vertices, heights)
        assert before['stats']['disc_count'] == after['stats']['disc_count']
        assert verify_cocycle_span(vertices, heights, before['certificate'])
        assert verify_cocycle_span(vertices, heights, after['certificate'])
        comparisons.append(dict(tetrahedra=n, old=compact(before), new=compact(after),
                                coordinates_equal=before['coordinates'] == after['coordinates']))
    entries = json.loads(SOURCE.read_text())['cases']
    previous = {r['source']['name']: r['results'] for r in json.loads(PREVIOUS.read_text())['source_cases']}
    cases, proofs, controls, optimizations = [], {}, [], []
    for entry in entries:
        source = entry['source']; diagram = Diagram.from_pd(source['pd'])
        results = {}
        for label, trials in (('default', 4), ('extended', 24)):
            answer = normal_seed_decide(diagram, tree_trials=trials)
            if answer['status'] == 'UNKNOT':
                assert source['expected'] == 'UNKNOT'
                assert verify_normal_seed_certificate(diagram, answer['certificate'])
                proof = answer.pop('certificate'); key = seeds.digest(proof)
                answer['certificate_sha256'] = key
                answer['old_certificate_sha256'] = previous[source['name']][label].get('certificate_sha256')
                if key != answer['old_certificate_sha256']:
                    proofs[key] = proof
            if previous[source['name']][label]['status'] == 'UNKNOT':
                assert answer['status'] == 'UNKNOT'
            results[label] = answer
        cases.append(dict(source=source, previous={label: dict(status=r['status'], work=r['work'])
                                                  for label, r in previous[source['name']].items()}, results=results))
        print(source['name'], [(k, v['status'], v['work']) for k, v in results.items()], flush=True)
        raw = diagram_exterior(diagram); seed = rank_one_cocycle_seed(raw)
        compared, successful = {}, {}
        for label, optimize in (('old', old), ('new', minimize_cocycle_span)):
            try:
                result = optimize(seed['vertices'], seed['heights'], max_work=2000000)
            except CocycleLimit:
                compared[label] = dict(status='CAPPED')
                continue
            assert verify_cocycle_span(seed['vertices'], seed['heights'], result['certificate'])
            compared[label] = dict(status='COMPLETE', **compact(result))
            successful[label] = result
        if len(successful) == 2:
            assert successful['old']['stats']['disc_count'] == successful['new']['stats']['disc_count']
            compared['coordinates_equal'] = successful['old']['coordinates'] == successful['new']['coordinates']
        optimizations.append(dict(name=source['name'], **compared))
        if len(source['pd']) <= 12:
            optimum = successful['new']
            proof = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(r) for r in diagram.pd],
                         triangulation=raw, heights=seed['heights'], coordinates=optimum['coordinates'],
                         span_certificate=optimum['certificate'])
            summary = inspect_cocycle_certificate(diagram, proof)
            surface = regina_surface(regina_triangulation(raw), optimum['coordinates'])
            components = surface.components()
            discs = sum(int(str(s.eulerChar())) == 1 and s.isCompressingDisc(True) for s in components)
            assert summary['components'] == len(components) == 1
            assert surface.isOrientable()
            assert summary['euler_characteristic'] == int(str(surface.eulerChar()))
            assert summary['compressing_discs'] == discs
            controls.append(dict(name=source['name'], **summary))
    ordinary = []
    for source in forests.corpus():
        results = []
        for label, optimize in (('old', old), ('new', minimize_cocycle_span)):
            with patch('fastunknot.normal_seed.minimize_cocycle_span', optimize):
                result = recognize(Diagram.from_pd(source['pd']), **seeds.COMMON, use_normal_seed=True)
            assert result.status == source['expected']
            results.append(dict(engine=label, status=result.status, method=result.method,
                                native_attempts=len(list(seeds.native_stages(result.evidence)))))
        ordinary.append(dict(name=source['name'], results=results))
    return dict(abstract_comparisons=comparisons, source_cases=cases, changed_source_proofs=proofs,
                source_optimizations=optimizations, regina_controls=controls, ordinary_pipeline=ordinary)


def benchmark(old, mode, rounds):
    if mode == 'optimize':
        cases = [(f'equal-{n}', ('equal', n, 0)) for n in (32, 128, 512)]
        cases += [('distinct-128', ('distinct', 128, 0)),
                  ('random-suite', ('random', 24, 0)),
                  ('circle-32', ('circle', 32, 0)), ('circle-4-binary', ('circle', 4, 4096))]
        def run(case, use_old):
            kind, n, bits = case
            if kind == 'random':
                # Aggregate complete small calls to make timer noise visible
                # against a workload where equal-cost batches are scarce.
                rng = random.Random(261009476)
                answers, totals = [], {}
                for _ in range(24):
                    vertices = [[rng.randrange(12) for _ in range(4)] for _ in range(n)]
                    heights = [[rng.randrange(-100, 101) for _ in range(4)] for _ in range(n)]
                    answer = (old if use_old else minimize_cocycle_span)(vertices, heights)
                    assert verify_cocycle_span(vertices, heights, answer['certificate'])
                    answers.append(answer)
                    for key, value in answer['stats'].items(): totals[key] = totals.get(key, 0)+value
                return dict(completed=True, stats=totals,
                            certificate_sha256=seeds.digest([a['certificate'] for a in answers]),
                            coordinates_sha256=seeds.digest([a['coordinates'] for a in answers]))
            if kind == 'equal':
                vertices, heights = [[0, 1, 2, 3]]*n, [[0, 0, 0, 0]]*n
            elif kind == 'distinct':
                vertices, heights = [[i]*4 for i in range(n)], [[0, 0, 0, i] for i in range(n)]
            else:
                raw = diagram_exterior(Diagram.from_braid(n+1, list(range(1, n+1))))
                seed = rank_one_cocycle_seed(raw)
                vertices, heights = seed['vertices'], [[h*(1 << bits) for h in row] for row in seed['heights']]
            answer = (old if use_old else minimize_cocycle_span)(vertices, heights)
            assert verify_cocycle_span(vertices, heights, answer['certificate'])
            return dict(completed=True, **compact(answer))
    else:
        entries = {e['source']['name']: e['source']['pd'] for e in json.loads(SOURCE.read_text())['cases']}
        cases = [('raw-circle', (Diagram.from_braid(9, list(range(1, 9))).pd, 4)),
                 ('optimized-positive', (entries['optimized-positive'], 4)),
                 ('early-two', (entries['random-99'], 4)), ('late-24', (entries['random-81'], 24)),
                 ('genus-one-miss', (Diagram.from_braid(2, [1, 1, -1]).pd, 4)),
                 ('trefoil', (Diagram.from_braid(2, [1, 1, 1]).pd, 4))]
        def run(case, use_old):
            pd, trials = case
            with patch('fastunknot.normal_seed.minimize_cocycle_span', old if use_old else minimize_cocycle_span):
                diagram = Diagram.from_pd(pd)
                result = recognize(diagram, **seeds.FORCED, normal_seed_tree_trials=trials)
                native = result.evidence.get('normal_seed', {}); proof = native.get('certificate')
                if proof is not None: assert verify_normal_seed_certificate(diagram, proof)
            completed = result.status in ('UNKNOT', 'KNOTTED')
            if completed: assert result.status == ('KNOTTED' if pd == cases[-1][1][0] else 'UNKNOT')
            return dict(completed=completed, status=result.status, method=result.method,
                        native_status=native.get('status'), native_work=native.get('work'),
                        optimization=native.get('stats', {}).get('optimization'),
                        certificate_sha256=seeds.digest(proof) if proof else None,
                        coordinates_sha256=seeds.digest(proof['coordinates']) if proof else None)
    return seeds.rounds(cases, run, rounds)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'optimize', 'recognize'))
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 1: parser.error('rounds must be positive')
    old, digest = baseline()
    before = pins(); start = time.perf_counter()
    result = audit(old) if args.mode == 'audit' else benchmark(old, args.mode, args.rounds)
    elapsed = time.perf_counter()-start
    assert pins() == before
    result.update(mode=args.mode, source_sha256=before, baseline_commit=BASELINE,
                  baseline_module_sha256=digest, elapsed_seconds=elapsed,
                  python=platform.python_version(), platform=platform.platform(), seed=261009475)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(seeds.json_safe(result), indent=2)+'\n')
    print(args.mode, 'complete', elapsed, flush=True)


if __name__ == '__main__':
    main()
