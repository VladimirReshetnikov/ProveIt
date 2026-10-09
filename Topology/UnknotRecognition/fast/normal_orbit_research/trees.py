"""Coverage and complete recognition costs of bounded alternative tree gauges."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import time
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.cocycle_trees import cocycle_tree_candidates
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from normal_orbit_research import seeds, connectivity
from normal_orbit_research.fixtures import regina_triangulation, regina_surface
from primitive_power_research import forests

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '48ef0ccef3f025e465657ef402cd370bb51d3b1d'
SOURCE = ROOT.parent/'synthesis/data/cocycle-seed-audit.json'
PREVIOUS = ROOT.parent/'synthesis/data/cocycle-connectivity-audit.json'


def pins():
    result = seeds.sources()
    for path in (SOURCE, PREVIOUS):
        result[str(path.relative_to(ROOT.parent))] = sha256(path.read_bytes()).hexdigest()
    return result


def audit():
    entries = json.loads(SOURCE.read_text())['cases']
    previous_data = json.loads(PREVIOUS.read_text())
    previous = {r['name']: r['result'] for r in previous_data['source_cases']}
    cases, proofs, control_inputs = [], {}, []
    for entry in entries:
        source = entry['source']; diagram = Diagram.from_pd(source['pd'])
        results = {}
        for label, trials in (('zero', 0), ('default', 4), ('extended', 24)):
            answer = normal_seed_decide(diagram, tree_trials=trials)
            if answer['status'] == 'UNKNOT':
                assert source['expected'] == 'UNKNOT'
                assert verify_normal_seed_certificate(diagram, answer['certificate'])
                proof = answer.pop('certificate'); key = seeds.digest(proof)
                if previous[source['name']]['status'] == 'UNKNOT':
                    assert key == previous[source['name']]['certificate_sha256']
                else:
                    proofs[key] = proof
                answer['certificate_sha256'] = key
            if label == 'zero':
                assert answer['status'] == previous[source['name']]['status']
            elif results['zero']['status'] == 'UNKNOT':
                assert answer['status'] == 'UNKNOT'
            if label == 'extended' and results['default']['status'] == 'UNKNOT':
                assert answer['status'] == 'UNKNOT'
            results[label] = answer
        if results['zero']['status'] != 'UNKNOT' and results['extended']['status'] == 'UNKNOT':
            control_inputs.append((source['name'], diagram))
        cases.append(dict(source=source, previous_work=previous[source['name']]['work'], results=results))
        print(source['name'], [(k, v['status'], v['work']) for k, v in results.items()], flush=True)
    control_inputs += [('trefoil', Diagram.from_braid(2, [1, 1, 1])),
                       ('genus-one-miss', Diagram.from_braid(2, [1, 1, -1])),
                       ('figure-eight', Diagram.from_braid(3, [1, -2, 1, -2]))]
    controls = []
    for name, diagram in control_inputs:
        raw = diagram_exterior(diagram); seed = rank_one_cocycle_seed(raw)
        tri = regina_triangulation(raw)
        for candidate in cocycle_tree_candidates(raw, seed['heights'], trials=24):
            if candidate['duplicate']: continue
            proof = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(r) for r in diagram.pd],
                         triangulation=raw, heights=candidate['heights'], coordinates=candidate['coordinates'],
                         span_certificate=None)
            summary = inspect_cocycle_certificate(diagram, proof)
            surface = regina_surface(tri, candidate['coordinates']); components = surface.components()
            discs = sum(int(str(s.eulerChar())) == 1 and s.isCompressingDisc(True) for s in components)
            assert summary['components'] == len(components) == 1
            assert surface.isOrientable()
            assert summary['euler_characteristic'] == int(str(surface.eulerChar())) == candidate['euler_characteristic']
            assert summary['compressing_discs'] == discs
            controls.append(dict(name=name, trial=candidate['trial'], **summary,
                                 coordinates_sha256=seeds.digest(candidate['coordinates'])))
    ordinary = []
    for source in forests.corpus():
        results = []
        for trials in (0, 4, 24):
            result = recognize(Diagram.from_pd(source['pd']), **seeds.COMMON,
                               use_normal_seed=True, normal_seed_tree_trials=trials)
            assert result.status == source['expected']
            results.append(dict(trials=trials, status=result.status, method=result.method,
                                native_attempts=len(list(seeds.native_stages(result.evidence)))))
        ordinary.append(dict(name=source['name'], results=results))
    return dict(source_cases=cases, new_certificates=proofs, regina_controls=controls,
                ordinary_pipeline=ordinary)


def benchmark(old, rounds):
    entries = {e['source']['name']: e['source']['pd'] for e in json.loads(SOURCE.read_text())['cases']}
    cases = [('raw-circle', (Diagram.from_braid(9, list(range(1, 9))).pd, 4)),
             ('optimized-positive', (entries['optimized-positive'], 4)),
             ('early-two', (entries['random-99'], 4)),
             ('early-three', (entries['random-29'], 4)),
             ('early-five', (entries['random-124'], 4)),
             ('late-24', (entries['random-81'], 24)),
             ('genus-one-miss', (Diagram.from_braid(2, [1, 1, -1]).pd, 4)),
             ('trefoil', (Diagram.from_braid(2, [1, 1, 1]).pd, 4))]
    def run(case, use_old):
        pd, trials = case
        def baseline(diagram, **kwargs):
            kwargs.pop('tree_trials', None)
            return old(diagram, **kwargs)
        with patch('fastunknot.normal_seed.normal_seed_decide', baseline if use_old else normal_seed_decide):
            diagram = Diagram.from_pd(pd)
            result = recognize(diagram, **seeds.FORCED, normal_seed_tree_trials=trials)
            native = result.evidence.get('normal_seed', {})
            proof = native.get('certificate')
            if proof is not None:
                assert verify_normal_seed_certificate(diagram, proof)
        completed = result.status in ('UNKNOT', 'KNOTTED')
        if completed:
            assert result.status == ('KNOTTED' if pd == cases[-1][1][0] else 'UNKNOT')
        return dict(completed=completed, status=result.status, method=result.method,
                    tree_trials=0 if use_old else trials,
                    native_status=native.get('status'), native_work=native.get('work'),
                    stages=[{k: v for k, v in s.items() if k != 'certificate'} for s in native.get('stages', [])],
                    certificate_sha256=seeds.digest(proof) if proof else None,
                    certificate_bytes=len(seeds.encode(proof)) if proof else None)
    return seeds.rounds(cases, run, rounds)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'recognize'))
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 1: parser.error('rounds must be positive')
    connectivity.BASELINE = BASELINE
    modules, hashes = connectivity.baseline()
    before = pins(); start = time.perf_counter()
    result = audit() if args.mode == 'audit' else benchmark(modules[0].normal_seed_decide, args.rounds)
    elapsed = time.perf_counter()-start
    assert pins() == before
    result.update(mode=args.mode, source_sha256=before, baseline_commit=BASELINE,
                  baseline_module_sha256=hashes, elapsed_seconds=elapsed,
                  python=platform.python_version(), platform=platform.platform(), tree_random_seed=261009471)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(args.mode, 'complete', elapsed, flush=True)


if __name__ == '__main__':
    main()
