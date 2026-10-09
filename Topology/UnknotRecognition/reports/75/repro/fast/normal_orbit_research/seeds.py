"""Pinned cocycle optimization, source-disc discovery and portfolio evidence."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, DiagramError, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.integer_codec import json_safe
from normal_orbit_research.fixtures import regina_triangulation, regina_surface
from primitive_power_research import forests as harness

BASELINE = '535a914a6904017912a3ae2b49f53db186498f70'
REPORT = ROOT.parent/'reports/31'
DELIVERY = REPORT/'integration/tree/Topology/UnknotRecognition/fast/fastunknot/cocycle_seed.py'
SEED = 261009460
FORCED = dict(use_reduction=False, use_descending=False, use_seifert=False,
              use_braid=False, use_rational=False, use_factorization=False,
              use_modular=False, use_jones=False, use_alexander=False, use_r3=False,
              use_normal_seed=True, normal_seed_max_work=None, max_objects=20000, seconds=12)
COMMON = dict(use_group=True, group_primitive_projection=True, group_relators=True,
              group_compressed_search=True, group_seconds=10, group_max_work=20000000,
              seconds=12, max_objects=50000)


def encode(value):
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return sha256(encode(value)).hexdigest()


def sources():
    paths = list(ROOT.rglob('*.py')) + [harness.CORPUS, DELIVERY, REPORT/'release-manifest.json',
        REPORT/'integration/tree/Topology/UnknotRecognition/fast/tests/test_cocycle_seed.py']
    return {str(p.relative_to(ROOT.parent)): sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def delivered():
    spec = importlib.util.spec_from_file_location('_cocycle_report31', DELIVERY)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def old_optimizer(vertices, heights, *, check=lambda: None, **unused):
    result = delivered_module.minimize_disc_seed(vertices, heights, check=check)
    proof = dict(schema='normal-cocycle-span-v1', vertex_ids=list(result.vertex_ids),
                 potential=list(result.potential), matching=[list(r) for r in result.matching],
                 coordinates=[list(r) for r in result.normal_coordinates], disc_count=result.disc_count)
    assert verify_cocycle_span(vertices, heights, proof, check=check)
    return dict(coordinates=proof['coordinates'], certificate=proof,
                stats=dict(result.statistics, disc_count=result.disc_count,
                           initial_disc_count=result.initial_disc_count))


def native_stages(evidence):
    pending = [evidence]
    while pending:
        item = pending.pop()
        if isinstance(item, dict):
            if item.get('method') == 'native-normal-cocycle': yield item
            pending.extend(v for v in item.values() if isinstance(v, (dict, list)))
        elif isinstance(item, list): pending.extend(item)


def audit(old):
    manifest = json.loads((REPORT/'release-manifest.json').read_text())
    for row in manifest['files']:
        assert sha256((REPORT/row['path']).read_bytes()).hexdigest() == row['sha256']
    rng = random.Random(SEED+3)
    comparisons = []
    for trial in range(200):
        n, k = rng.randrange(1, 15), rng.randrange(1, 10)
        vertices = [[rng.randrange(k) for _ in range(4)] for _ in range(n)]
        heights = [[rng.randrange(-50, 51) for _ in range(4)] for _ in range(n)]
        if trial == 199: heights = [[h*(1 << 20000) for h in row] for row in heights]
        before, after = old_optimizer(vertices, heights), minimize_cocycle_span(vertices, heights)
        assert before['stats']['disc_count'] == after['stats']['disc_count']
        assert verify_cocycle_span(vertices, heights, before['certificate'])
        assert verify_cocycle_span(vertices, heights, after['certificate'])
        comparisons.append(dict(tetrahedra=n, height_bits=max(abs(h).bit_length() for r in heights for h in r),
                                disc_count=after['stats']['disc_count'], old_stats=before['stats'],
                                new_stats=after['stats'], old_proof=digest(before['certificate']),
                                new_proof=digest(after['certificate'])))
    inputs = [dict(name=r['name'], pd=r['pd'], expected=r['expected']) for r in harness.corpus()]
    inputs += [dict(name='empty-circle', pd=[], expected='UNKNOT'),
               dict(name='optimized-positive', pd=Diagram.from_braid(4, [-1, 2, 1, -2, 3]).pd, expected='UNKNOT')]
    rng = random.Random(SEED)
    for i in range(180):
        strands = rng.randrange(2, 5)
        word = [rng.choice((-1, 1))*rng.randrange(1, strands) for _ in range(rng.randrange(1, 13))]
        try: d = Diagram.from_braid(strands, word)
        except DiagramError: continue
        reference = recognize(d, seconds=10, max_objects=50000)
        assert reference.status in ('UNKNOT', 'KNOTTED')
        inputs.append(dict(name=f'random-{i}', pd=d.pd, expected=reference.status))
    for strands in (9, 17, 33):
        inputs.append(dict(name=f'circle-{strands}', pd=Diagram.from_braid(strands, list(range(1, strands))).pd,
                           expected='UNKNOT'))
    cases, proofs, replays = [], {}, 0
    for source in inputs:
        d = Diagram.from_pd(source['pd'])
        answer = normal_seed_decide(d)
        if answer['status'] == 'UNKNOT':
            assert source['expected'] == 'UNKNOT'
            assert verify_normal_seed_certificate(d, answer['certificate'])
            replays += 1
            proof = answer.pop('certificate')
            key = digest(proof)
            # Retain full source proofs once; many curl/circle inputs coincide.
            proofs[key] = proof
            answer['certificate_sha256'] = key
        cases.append(dict(source=source, result=answer))
    controls = []
    for source in inputs:
        if len(source['pd']) > 12: continue
        d = Diagram.from_pd(source['pd']); raw = diagram_exterior(d)
        seed = rank_one_cocycle_seed(raw)
        optimized = minimize_cocycle_span(seed['vertices'], seed['heights'])
        tri = regina_triangulation(raw)
        for label, vector in [('raw', seed['coordinates']), ('optimized', optimized['coordinates'])]:
            census = normal_component_census(raw, vector, mode='summary')
            surface = regina_surface(tri, vector)
            components = surface.components()
            discs = sum(int(str(s.eulerChar())) == 1 and s.isCompressingDisc(True) for s in components)
            assert census['compressing_disk_components'] == discs
            assert census['components'] == len(components)
            assert sum(r['multiplicity']*r['euler_characteristic'] for r in census['component_histogram']) == int(str(surface.eulerChar()))
            assert label != 'optimized' or len(components) == 1
            controls.append(dict(name=source['name'], seed=label, components=len(components),
                                 compressing_discs=discs, euler=int(str(surface.eulerChar()))))
    ordinary = []
    for source in harness.corpus():
        results = []
        for label, engine, options in [('old', old, COMMON), ('current', sys.modules['fastunknot'], COMMON),
                                      ('enabled', sys.modules['fastunknot'], dict(COMMON, use_normal_seed=True))]:
            r = engine.recognize(engine.Diagram.from_pd(source['pd']), **options)
            assert r.status == source['expected']
            results.append(dict(engine=label, status=r.status, method=r.method,
                                native_attempts=len(list(native_stages(r.evidence)))))
        ordinary.append(dict(name=source['name'], results=results))
    return dict(delivered_manifest_entries=len(manifest['files']), algebraic_comparisons=comparisons,
                cases=cases, certificates=proofs, source_replays=replays, regina_component_controls=controls,
                ordinary_pipeline=ordinary)


def measure(function):
    start = time.perf_counter()
    record = function()
    return dict(seconds=time.perf_counter()-start, **record)


def rounds(cases, make, count):
    rng = random.Random(SEED+4); records = []
    for name, value in cases:
        samples, warmups = [], []
        for iteration in range(-1, count):
            order = ['old', 'old_AA', 'new', 'new_AA']; rng.shuffle(order)
            results = {arm: measure(lambda: make(value, arm.startswith('old'))) for arm in order}
            (warmups if iteration < 0 else samples).append(dict(order=order, measurements=results))
        arms = ('old', 'old_AA', 'new', 'new_AA')
        medians = {a: median(s['measurements'][a]['seconds'] for s in samples
                             if s['measurements'][a]['completed']) if any(s['measurements'][a]['completed'] for s in samples) else None for a in arms}
        pairs = {}
        for label, a, b in (('old_new', 'old', 'new'), ('old_AA', 'old', 'old_AA'), ('new_AA', 'new', 'new_AA')):
            values = [s['measurements'][a]['seconds']/s['measurements'][b]['seconds'] for s in samples
                      if s['measurements'][a]['completed'] and s['measurements'][b]['completed']]
            pairs[label] = dict(count=len(values), median=median(values) if values else None)
        records.append(dict(name=name, samples=samples, warmups=warmups, medians=medians, paired_ratios=pairs))
        print(name, json.dumps(pairs), flush=True)
    return dict(cases=records, measured_calls=len(cases)*count*4, warmup_calls=len(cases)*4,
                completed_calls=sum(m['completed'] for r in records for s in r['samples'] for m in s['measurements'].values()))


def optimize_benchmark(count):
    def run(case, use_old):
        crossings, bits = case
        d = Diagram.from_braid(crossings+1, list(range(1, crossings+1)))
        raw = diagram_exterior(d); assert verify_diagram_exterior(d, raw)
        seed = rank_one_cocycle_seed(raw)
        heights = [[h+((v % 7)-3)*(1 << bits) for v, h in zip(vs, hs)]
                   for vs, hs in zip(seed['vertices'], seed['heights'])] if bits else seed['heights']
        result = (old_optimizer if use_old else minimize_cocycle_span)(seed['vertices'], heights)
        assert verify_cocycle_span(seed['vertices'], heights, result['certificate'])
        _coordinates(_prepare(raw, lambda: None), result['coordinates'], lambda: None)
        return dict(completed=True, stats=result['stats'], certificate_sha256=digest(result['certificate']))
    return rounds([(f'circle-{n}-bits-{b}', (n, b)) for n, b in ((1, 0), (4, 0), (8, 0), (16, 0), (4, 4096))], run, count)


def source_benchmark(count):
    cases = [('raw-circle', (9, list(range(1, 9)), 'UNKNOT')),
             ('optimized-positive', (4, [-1, 2, 1, -2, 3], 'UNKNOT')),
             ('genus-one-miss', (2, [1, 1, -1], 'UNKNOT')),
             ('trefoil', (2, [1, 1, 1], 'KNOTTED')),
             ('figure-eight', (3, [1, -2, 1, -2], 'KNOTTED'))]
    def run(case, use_old):
        strands, word, expected = case
        with patch('fastunknot.normal_seed.minimize_cocycle_span', old_optimizer if use_old else minimize_cocycle_span):
            r = recognize(Diagram.from_braid(strands, word), **FORCED)
        complete = r.status in ('UNKNOT', 'KNOTTED')
        if complete: assert r.status == expected
        stages = [{k: v for k, v in row.items() if k != 'certificate'} for row in native_stages(r.evidence)]
        return dict(completed=complete, status=r.status, method=r.method, stages=stages)
    return rounds(cases, run, count)


def pipeline_benchmark(old, count):
    def run(source, use_old):
        engine = old if use_old else sys.modules['fastunknot']
        r = engine.recognize(engine.Diagram.from_pd(source['pd']), **COMMON,
                             **({} if use_old else dict(use_normal_seed=True)))
        complete = r.status in ('UNKNOT', 'KNOTTED')
        if complete: assert r.status == source['expected']
        return dict(completed=complete, status=r.status, method=r.method,
                    native_attempts=len(list(native_stages(r.evidence))))
    return rounds([(s['name'], dict(name=s['name'], pd=s['pd'], expected=s['expected'])) for s in harness.corpus()], run, count)


def main():
    global delivered_module
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('audit', 'optimize', 'source', 'pipeline'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1: parser.error('rounds must be positive')
    before = sources(); delivered_module = delivered(); harness.BASELINE = BASELINE
    with tempfile.TemporaryDirectory(prefix='unknot-seed-baseline-') as temporary:
        old, _, _, hashes = harness.baseline(temporary)
        begin = time.perf_counter()
        if args.mode == 'audit': result = audit(old)
        elif args.mode == 'optimize': result = optimize_benchmark(args.rounds)
        elif args.mode == 'source': result = source_benchmark(args.rounds)
        else: result = pipeline_benchmark(old, args.rounds)
        result.update(mode=args.mode, elapsed_seconds=time.perf_counter()-begin,
                      python=sys.version, platform=platform.platform(), seed=SEED,
                      source_sha256=before, baseline_commit=BASELINE, baseline_source_sha256=hashes)
    assert sources() == before, 'sources changed during run'
    args.output.write_bytes(json.dumps(json_safe(result), indent=2).encode()+b'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in (
        'cases', 'certificates', 'source_sha256', 'baseline_source_sha256', 'ordinary_pipeline',
        'algebraic_comparisons', 'regina_component_controls')}, indent=2))


if __name__ == '__main__':
    main()
