"""Reproduce canonical source-exterior checks and complete construction costs."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import time

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


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def sources():
    return {str(p.relative_to(ROOT.parent)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(list(ROOT.rglob('*.py')) + [CORPUS])}


def audit():
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
            raw = diagram_exterior(diagram)
            assert verify_diagram_exterior(diagram, raw)
            prepared = _prepare(raw, lambda: None)
            compact = regina_triangulation(raw)
            assert compact.isValid() and compact.isOrientable() and not compact.isIdeal()
            assert compact.countBoundaryComponents() == 1
            assert compact.boundaryComponent(0).eulerChar() == 0
            corner = regina_triangulation(dict(tetrahedra=_corner_triangulation(diagram, lambda: None)))
            link = regina.Link.fromPD(regina_pd(diagram)) if diagram.pd else regina.Link(1)
            oracle = link.complement(False)
            assert corner.isIsomorphicTo(oracle) is not None
            assert sorted(v.linkEulerChar() for v in corner.vertices()) == [0, 2, 2]
            cases.append(dict(name=name, variant=variant, pd=diagram.pd,
                              finite_sha256=digest(raw), mixed_sha256=digest(dict(tetrahedra=_corner_triangulation(diagram, lambda: None))),
                              crossings=diagram.crossings, tetrahedra=compact.size(),
                              boundary_triangles=len(prepared['boundary_faces']),
                              source_replay=True, native_manifold=True,
                              regina_finite_manifold=True, regina_mixed_isomorphism=True))
    return dict(cases=cases, source_diagrams=len(inputs), source_replays=len(cases),
                regina_version=regina.versionString(), regina_distribution=version('regina'),
                all_complete=True)


def operation(diagram):
    start = time.perf_counter_ns()
    raw = diagram_exterior(diagram)
    assert verify_diagram_exterior(diagram, raw)
    prepared = _prepare(raw, lambda: None)
    elapsed = (time.perf_counter_ns() - start)/1e9
    return dict(seconds=elapsed, sha256=digest(raw), tetrahedra=len(raw['tetrahedra']),
                boundary_triangles=len(prepared['boundary_faces']))


def benchmark(rounds):
    cases = []
    for n in (1, 8, 32, 128):
        diagram = Diagram.from_braid(n+1, list(range(1, n+1)))
        warm = [operation(diagram), operation(diagram)]
        runs = []
        for r in range(rounds):
            pair = {}
            for arm in (('A', 'AA') if r % 2 == 0 else ('AA', 'A')):
                pair[arm] = operation(diagram)
            runs.append(pair)
        hashes = {record['sha256'] for record in warm}
        hashes.update(record['sha256'] for pair in runs for record in pair.values())
        assert len(hashes) == 1
        cases.append(dict(crossings=n, warmup=warm, runs=runs,
                          median_A=median(pair['A']['seconds'] for pair in runs),
                          median_AA=median(pair['AA']['seconds'] for pair in runs),
                          paired_A_over_AA=median(pair['A']['seconds']/pair['AA']['seconds'] for pair in runs)))
    return dict(cases=cases, rounds=rounds, measured_calls=8*rounds, warmup_calls=8,
                endpoint='fresh native construction + independent source replay + native finite-manifold validation',
                comparison='same implementation A/A control; no predecessor or recognition speedup claimed',
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
    start = time.perf_counter()
    result = audit() if args.mode == 'audit' else benchmark(args.rounds)
    result.update(mode=args.mode, seed=SEED, elapsed_seconds=time.perf_counter()-start,
                  python=sys.version, platform=platform.platform(), source_sha256=before)
    assert sources() == before, 'sources changed during run'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('cases', 'source_sha256')}, indent=2))


if __name__ == '__main__':
    main()
