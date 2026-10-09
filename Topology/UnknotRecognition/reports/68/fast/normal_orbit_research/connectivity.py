"""Source-bound cocycle connectivity against orbit and Regina controls."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation, regina_surface
from primitive_power_research import forests

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '6212f6f69e88ac51a4d1e40a287a69935a9260ea'
SOURCE = ROOT.parent/'synthesis/data/cocycle-seed-audit.json'
PREVIOUS = ROOT.parent/'synthesis/data/single-orbit-audit.json'


def baseline():
    modules, hashes = [], {}
    for name in ('normal_seed', 'normal_seed_verify'):
        path = 'Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        source = subprocess.check_output(['git', 'show', BASELINE+':'+path], cwd=ROOT)
        module = ModuleType('_connectivity_baseline_'+name)
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
    source_data = json.loads(SOURCE.read_text())
    previous = {r['name']: r['result'] for r in json.loads(PREVIOUS.read_text())['source_cases']}
    cases, proofs, controls = [], {}, []
    for entry in source_data['cases']:
        source = entry['source']; diagram = Diagram.from_pd(source['pd'])
        answer = normal_seed_decide(diagram)
        if answer['status'] == 'UNKNOT':
            assert source['expected'] == 'UNKNOT'
            assert verify_normal_seed_certificate(diagram, answer['certificate'])
            proof = answer.pop('certificate'); key = seeds.digest(proof)
            proofs[key] = proof
            answer['certificate_sha256'] = key
            answer['certificate_bytes'] = len(seeds.encode(proof))
        if previous[source['name']]['status'] == 'UNKNOT':
            assert answer['status'] == 'UNKNOT'
            legacy = source_data['certificates'][entry['result']['certificate_sha256']]
            assert old_verify(diagram, legacy)
            assert verify_normal_seed_certificate(diagram, legacy)
            assert seeds.digest(proof['coordinates']) == seeds.digest(legacy['coordinates'])
            answer['old_certificate_bytes'] = len(seeds.encode(legacy))
        cases.append(dict(name=source['name'], crossings=len(source['pd']),
                          expected=source['expected'], old_status=previous[source['name']]['status'],
                          old_work=previous[source['name']]['work'], result=answer))
        print(source['name'], answer['status'], answer['work'], flush=True)
        if len(source['pd']) > 12:
            continue
        raw = diagram_exterior(diagram); seed = rank_one_cocycle_seed(raw)
        optimum = minimize_cocycle_span(seed['vertices'], seed['heights'])
        tri = regina_triangulation(raw)
        for label, vector, span in (('raw', seed['coordinates'], None),
                                    ('optimized', optimum['coordinates'], optimum['certificate'])):
            proof = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(r) for r in diagram.pd],
                         triangulation=raw, heights=seed['heights'], coordinates=vector, span_certificate=span)
            summary = inspect_cocycle_certificate(diagram, proof)
            assert summary is not None
            surface = regina_surface(tri, vector); components = surface.components()
            discs = sum(int(str(s.eulerChar())) == 1 and s.isCompressingDisc(True) for s in components)
            assert summary['components'] == len(components) == 1
            assert summary['orientable_components'] == int(surface.isOrientable()) == 1
            assert summary['euler_characteristic'] == int(str(surface.eulerChar()))
            assert summary['compressing_discs'] == discs
            controls.append(dict(name=source['name'], stage=label, **summary))
    ordinary = []
    for source in forests.corpus():
        results = []
        for label, producer, verifier, enabled in (('old', old, old_verify, True),
                ('new-disabled', normal_seed_decide, verify_normal_seed_certificate, False),
                ('new-enabled', normal_seed_decide, verify_normal_seed_certificate, True)):
            with patch('fastunknot.normal_seed.normal_seed_decide', producer), \
                 patch('fastunknot.normal_seed_verify.verify_normal_seed_certificate', verifier):
                result = recognize(Diagram.from_pd(source['pd']), **seeds.COMMON, use_normal_seed=enabled)
            assert result.status == source['expected']
            results.append(dict(engine=label, status=result.status, method=result.method,
                                native_attempts=len(list(seeds.native_stages(result.evidence)))))
        ordinary.append(dict(name=source['name'], results=results))
    return dict(source_cases=cases, certificates=proofs, regina_controls=controls,
                source_replays=sum(r['result']['status'] == 'UNKNOT' for r in cases), ordinary_pipeline=ordinary)


def benchmark(old, old_verify, mode, rounds):
    cases = [(f'circle-{n}', Diagram.from_braid(n+1, list(range(1, n+1))).pd) for n in (8, 16, 32)]
    cases += [('optimized-positive', Diagram.from_braid(4, [-1, 2, 1, -2, 3]).pd),
              ('genus-one-miss', Diagram.from_braid(2, [1, 1, -1]).pd),
              ('trefoil', Diagram.from_braid(2, [1, 1, 1]).pd)]
    if mode == 'replay':
        prepared = []
        for name, pd in cases[:-2]:
            diagram = Diagram.from_pd(pd)
            with patch('fastunknot.normal_seed_verify.verify_normal_seed_certificate', old_verify):
                before = old(diagram, max_work=None)
            after = normal_seed_decide(diagram, max_work=None)
            assert before['status'] == after['status'] == 'UNKNOT'
            assert before['certificate']['coordinates'] == after['certificate']['coordinates']
            prepared.append((name, (pd, before['certificate'], after['certificate'])))
        cases = prepared
        def run(case, use_old):
            pd, before, after = case
            proof = before if use_old else after
            verifier = old_verify if use_old else verify_normal_seed_certificate
            assert verifier(Diagram.from_pd(pd), proof)
            return dict(completed=True, certificate_sha256=seeds.digest(proof),
                        certificate_bytes=len(seeds.encode(proof)), coordinates_sha256=seeds.digest(proof['coordinates']))
    else:
        def run(pd, use_old):
            producer = old if use_old else normal_seed_decide
            verifier = old_verify if use_old else verify_normal_seed_certificate
            with patch('fastunknot.normal_seed.normal_seed_decide', producer), \
                 patch('fastunknot.normal_seed_verify.verify_normal_seed_certificate', verifier):
                diagram = Diagram.from_pd(pd)
                result = recognize(diagram, **seeds.FORCED)
                native = result.evidence.get('normal_seed', {})
                proof = native.get('certificate')
                if proof is not None:
                    assert verifier(diagram, proof)
            completed = result.status in ('UNKNOT', 'KNOTTED')
            if completed:
                assert result.status == ('KNOTTED' if pd == cases[-1][1] else 'UNKNOT')
            return dict(completed=completed, status=result.status, method=result.method,
                        native_status=native.get('status'), native_work=native.get('work'),
                        certificate_sha256=seeds.digest(proof) if proof else None,
                        certificate_bytes=len(seeds.encode(proof)) if proof else None,
                        coordinates_sha256=seeds.digest(proof['coordinates']) if proof else None)
    return seeds.rounds(cases, run, rounds)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'replay', 'recognize'))
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 1: parser.error('rounds must be positive')
    modules, hashes = baseline()
    old, old_verify = modules[0].normal_seed_decide, modules[1].verify_normal_seed_certificate
    before = pins(); start = time.perf_counter()
    result = audit(old, old_verify) if args.mode == 'audit' else benchmark(old, old_verify, args.mode, args.rounds)
    elapsed = time.perf_counter()-start
    assert pins() == before
    result.update(mode=args.mode, source_sha256=before, baseline_commit=BASELINE,
                  baseline_module_sha256=hashes, elapsed_seconds=elapsed,
                  python=platform.python_version(), platform=platform.platform())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(args.mode, 'complete', elapsed, flush=True)


if __name__ == '__main__':
    main()
