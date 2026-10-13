"""Pinned full-coordinate inventory audit and serial certified comparisons."""
import argparse
from hashlib import sha256
import importlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from primitive_power_research import forests as harness
from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus
from weighted_research.normal_audit import run_audit
BASELINE = 'aeb891e7159af76cd536502631571f29b5c1a401'
SEED = 261009441
CORPUS = ROOT.parent/'reports/53/results/normal_audit_20261009_corpus.json'


def sources():
    return {str(p.relative_to(ROOT.parent)): sha256(p.read_bytes()).hexdigest()
            for p in list(ROOT.rglob('*.py'))+[CORPUS, ROOT/'tests/fixtures/normal_component_v1.json']}


def encode(value):
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def audit(old_census):
    corpus = json.loads(CORPUS.read_text())
    result = run_audit(corpus, ROOT)
    assert not result['failures']
    triangulations = {t['id']: t for t in corpus['triangulations']}
    bounds = []
    for case in corpus['cases']:
        source = triangulations[case['triangulation_id']]
        raw, vector = source['triangulation'], case['coordinates']
        answer = normal_component_census(raw, vector, mode='coordinates', record_certificate=True)
        prior = old_census(raw, vector, mode='coordinates', record_certificate=True)
        assert prior['certificate']['summary'] == answer['certificate']['summary']
        assert verify_normal_component_certificate(raw, vector, prior['certificate'])
        assert prior['certificate']['weighted_orbits']['orbit_proof'] == answer['certificate']['weighted_orbits']['orbit_proof']
        expected = case['expected']['component_records']
        q = sum(bool(x) for row in vector for x in row[4:])
        v, h = source['vertices'], len(expected)
        two_sided = all(row['two_sided'] for row in expected)
        bound = v+(q if two_sided else 2*q)
        assert h <= bound
        assert answer['weight_dimension'] <= max(1, v+q)
        bounds.append(dict(case=case['id'], vertices=v, quad_support=q, types=h,
                           all_two_sided=two_sided, bound=bound, dimension=answer['weight_dimension'],
                           dense_dimension=prior['weight_dimension']))
    return dict(regina=result, dense_comparisons=len(bounds), legacy_replays=len(bounds),
                unchanged_orbit_proofs=len(bounds), component_type_bounds=bounds)


def cases():
    for t in (1,16,64,128):
        raw, vector = layered_torus(t)
        yield dict(name=f'meridian-{t}', triangulation=raw, coordinates=vector)
    raw, basis = interior_vertex_torus()
    vector = [[3*a+5*b for a,b in zip(left,right)]
              for left,right in zip(basis['sphere'],basis['boundary_disk'])]
    yield dict(name='triangle-only', triangulation=raw, coordinates=vector)
    raw, vector = layered_torus(8)
    scale = 1 << 1024
    vector = [[scale*x+(scale+1 if j<4 else 0) for j,x in enumerate(row)] for row in vector]
    yield dict(name='binary-1024', triangulation=raw, coordinates=vector)


def benchmark(old_census, old_verify):
    rng = random.Random(SEED+1)
    methods = {'old': (old_census,old_verify),
               'compact': (normal_component_census, verify_normal_component_certificate)}
    arms = ('old','old_AA','compact','compact_AA')
    records, proofs = [], {}
    for source in cases():
        samples, warmups, reference = [], [], None
        for iteration in range(-1,5):
            order = list(arms)
            rng.shuffle(order)
            measurements = {}
            for arm in order:
                census, verifier = methods[arm.removesuffix('_AA')]
                raw, vector = source['triangulation'], source['coordinates']
                begin = time.perf_counter()
                answer = census(raw, vector, mode='coordinates', record_certificate=True)
                middle = time.perf_counter()
                assert answer['status'] == 'COMPLETE'
                assert verifier(raw, vector, answer['certificate'])
                end = time.perf_counter()
                certificate = answer['certificate']
                if reference is None:
                    reference = certificate['summary']
                assert certificate['summary'] == reference
                encoded = encode(certificate)
                key = sha256(encoded).hexdigest()
                proofs[key] = certificate
                measurements[arm] = dict(seconds=end-begin, produce_seconds=middle-begin,
                    verify_seconds=end-middle, completed=True, certificate_sha256=key,
                    certificate_bytes=len(encoded), weight_dimension=answer['weight_dimension'],
                    stats=answer['stats'])
            (warmups if iteration<0 else samples).append(dict(order=order, measurements=measurements))
        medians = {arm: median(row['measurements'][arm]['seconds'] for row in samples) for arm in arms}
        ratios = {f'{a}/{b}': median(row['measurements'][a]['seconds']/row['measurements'][b]['seconds']
                                   for row in samples)
                  for a,b in (('old','compact'),('old','old_AA'),('compact','compact_AA'))}
        records.append(dict(source=source, samples=samples, warmups=warmups, medians=medians, paired_ratios=ratios))
        print(source['name'], ratios, flush=True)
    return dict(cases=records, certificates=proofs, measured_calls=len(records)*20,
                warmup_calls=len(records)*4, completed_calls=len(records)*20,
                scope='Complete full-coordinate census including fresh geometry, certificate production '
                      'and independent replay. Five shuffled rounds, A/A on both engines. Serialization '
                      'and equality checks outside timers. Supplied surfaces, not knot recognition.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit','benchmark'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    harness.BASELINE = BASELINE
    before = sources()
    begin = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-compact-coordinates-') as directory:
        package, _, _, hashes = harness.baseline(directory)
        changed = {name for name, value in hashes.items()
                   if value != sha256((ROOT/'fastunknot'/name).read_bytes()).hexdigest()}
        assert changed == {'normal_component_geometry.py','normal_surface_components.py','normal_component_verify.py'}, changed
        old_census = importlib.import_module(package.__name__+'.normal_surface_components').normal_component_census
        old_verify = importlib.import_module(package.__name__+'.normal_component_verify').verify_normal_component_certificate
        result = audit(old_census) if args.mode=='audit' else benchmark(old_census,old_verify)
    assert sources() == before
    result.update(mode=args.mode, baseline_commit=BASELINE, source_sha256=before,
                  baseline_source_sha256=hashes, source_hashes_unchanged=True, seed=SEED,
                  seconds=time.perf_counter()-begin, python=platform.python_version(), platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result), indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__ == '__main__':
    main()
