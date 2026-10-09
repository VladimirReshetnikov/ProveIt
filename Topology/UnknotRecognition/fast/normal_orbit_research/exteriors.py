"""Reproduce canonical source-exterior checks and complete construction costs."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
import time
from types import ModuleType

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot.diagram import Diagram, DiagramError
from fastunknot.diagram_exterior import diagram_exterior, _corner_triangulation
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_surface import regina_pd
from normal_orbit_research.fixtures import regina_triangulation

CORPUS = ROOT.parent / 'reports/46/repo_overlay/Topology/UnknotRecognition/fast/cyclic_overlap_research/results.json'
SEED = 261009459
BASELINE = '8354e8aab9a2d7f2b51bcd8423f0875e843f8406'


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def sources():
    return {str(p.relative_to(ROOT.parent)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(list(ROOT.rglob('*.py')) + [CORPUS])}


def baseline():
    modules, hashes = [], {}
    for name in ('diagram_exterior', 'diagram_exterior_verify'):
        path = 'Topology/UnknotRecognition/fast/fastunknot/' + name + '.py'
        raw = subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)
        module = ModuleType('_exterior_baseline_' + name)
        module.__package__ = 'fastunknot'
        exec(compile(raw, BASELINE + ':' + path, 'exec'), module.__dict__)
        modules.append(module)
        hashes[path] = sha256(raw).hexdigest()
    return modules[0].diagram_exterior, modules[1].verify_diagram_exterior, hashes


def audit(old_build, old_verify):
    import regina
    from importlib.metadata import version
    rng = random.Random(SEED)
    inputs = [(row['name'], Diagram.from_pd(row['pd']))
              for row in json.loads(CORPUS.read_text())['rows']]
    inputs.append(('empty-circle', Diagram.from_pd([])))
    for i in range(240):
        strands = rng.randrange(2, 7)
        word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 21))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except DiagramError:
            continue
        inputs.append((f'random-{i}', diagram))
    cases = []
    for name, source in inputs:
        for variant, diagram in (
                ('source', source), ('mirror', source.mirror()),
                ('port-rotation', Diagram.from_pd([row[2:]+row[:2] for row in reversed(source.pd)]))):
            corner = regina_triangulation(dict(tetrahedra=_corner_triangulation(diagram, lambda: None)))
            link = regina.Link.fromPD(regina_pd(diagram)) if diagram.pd else regina.Link(1)
            oracle = link.complement(False)
            assert corner.isIsomorphicTo(oracle) is not None
            assert sorted(v.linkEulerChar() for v in corner.vertices()) == [0, 2, 2]
            subdivisions = {}
            for subdivision in ('pulling', 'centred'):
                raw = diagram_exterior(diagram, subdivision=subdivision)
                assert verify_diagram_exterior(diagram, raw)
                prepared = _prepare(raw, lambda: None)
                compact = regina_triangulation(raw)
                assert compact.isValid() and compact.isOrientable() and not compact.isIdeal()
                assert compact.countBoundaryComponents() == 1
                assert compact.boundaryComponent(0).eulerChar() == 0
                if subdivision == 'centred':
                    assert raw == old_build(diagram)
                    assert old_verify(diagram, raw)
                subdivisions[subdivision] = dict(finite_sha256=digest(raw),
                    tetrahedra=compact.size(), boundary_triangles=len(prepared['boundary_faces']),
                    source_replay=True, native_manifold=True, regina_finite_manifold=True)
            cases.append(dict(name=name, variant=variant, pd=diagram.pd,
                              mixed_sha256=digest(dict(tetrahedra=_corner_triangulation(diagram, lambda: None))),
                              crossings=diagram.crossings, subdivisions=subdivisions,
                              regina_mixed_isomorphism=True))
    return dict(cases=cases, source_diagrams=len(inputs), source_variants=len(cases),
                source_replays=3*len(cases), finite_manifold_comparisons=2*len(cases),
                all_centred_outputs_identical_to_baseline=True,
                regina_version=regina.versionString(), regina_distribution=version('regina'),
                all_complete=True)


def operation(diagram, build, verify):
    start = time.perf_counter_ns()
    raw = build(diagram)
    assert verify(diagram, raw)
    prepared = _prepare(raw, lambda: None)
    elapsed = (time.perf_counter_ns() - start)/1e9
    return dict(seconds=elapsed, sha256=digest(raw), tetrahedra=len(raw['tetrahedra']),
                boundary_triangles=len(prepared['boundary_faces']))


def benchmark(rounds, old_build, old_verify):
    cases = []
    for n in (1, 8, 32, 128):
        diagram = Diagram.from_braid(n+1, list(range(1, n+1)))
        engines = {'old': (old_build, old_verify), 'old_AA': (old_build, old_verify),
                   'new': (diagram_exterior, verify_diagram_exterior),
                   'new_AA': (diagram_exterior, verify_diagram_exterior)}
        warm = {arm: operation(diagram, *engine) for arm, engine in engines.items()}
        runs = []
        for r in range(rounds):
            pair = {}
            order = list(engines)
            order = order[r % 4:] + order[:r % 4]
            if r % 2: order.reverse()
            for arm in order:
                pair[arm] = operation(diagram, *engines[arm])
            runs.append(pair)
        for prefix in ('old', 'new'):
            hashes = {warm[arm]['sha256'] for arm in (prefix, prefix+'_AA')}
            hashes.update(pair[arm]['sha256'] for pair in runs for arm in (prefix, prefix+'_AA'))
            assert len(hashes) == 1
        cases.append(dict(crossings=n, warmup=warm, runs=runs,
                          medians={arm: median(pair[arm]['seconds'] for pair in runs) for arm in engines},
                          paired_old_new=median(pair['old']['seconds']/pair['new']['seconds'] for pair in runs),
                          paired_old_AA=median(pair['old']['seconds']/pair['old_AA']['seconds'] for pair in runs),
                          paired_new_AA=median(pair['new']['seconds']/pair['new_AA']['seconds'] for pair in runs)))
    return dict(cases=cases, rounds=rounds, measured_calls=16*rounds, warmup_calls=16,
                endpoint='fresh native construction + independent source replay + native finite-manifold validation',
                comparison='first published centred implementation versus pulling subdivision; both complete source-exterior calls, each with an A/A control',
                all_complete=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('audit', 'benchmark'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('rounds must be positive')
    before = sources()
    old_build, old_verify, hashes = baseline()
    start = time.perf_counter()
    result = audit(old_build, old_verify) if args.mode == 'audit' else benchmark(args.rounds, old_build, old_verify)
    result.update(mode=args.mode, seed=SEED, elapsed_seconds=time.perf_counter()-start,
                  python=sys.version, platform=platform.platform(), source_sha256=before,
                  baseline_commit=BASELINE, baseline_source_sha256=hashes)
    assert sources() == before, 'sources changed during run'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('cases', 'source_sha256')}, indent=2))


if __name__ == '__main__':
    main()
