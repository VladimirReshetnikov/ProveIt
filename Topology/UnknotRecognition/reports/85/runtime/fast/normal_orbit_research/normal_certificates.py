"""Audit and time native normal topology proofs against pinned code and Regina.

Run from fast/: python -B normal_orbit_research/normal_certificates.py
    {audit,benchmark} --output FILE
"""
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys
import time
import types

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_orbits import normal_surface_topology as _native_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_surface_geometry import _prepare
from normal_orbit_research.fixtures import (
    layered_torus, boundary_cap, regina_triangulation, regina_surface, export_surface,
)

BASELINE = '98f21ce333bf1d5bdd0c630effd794cc88a33aec'
SEED = 261008496
ARCHIVE = ROOT.parent/'reports/47/snapshot/Topology/UnknotRecognition/fast/fastunknot'


def normal_surface_topology(*args, **kwargs):
    """Reproduce the version-one experiment without later multiplicity reduction."""
    return _native_topology(*args, reduce_multiplicity=False, **kwargs)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sources():
    paths = [ROOT/'fastunknot'/name for name in (
        'normal_surface_orbits.py', 'normal_surface_geometry.py',
        'normal_surface_parity.py', 'normal_surface_verify.py',
        'interval_orbits.py', 'interval_orbit_verify.py', 'integer_codec.py')]
    paths += [Path(__file__).resolve(), ROOT/'normal_orbit_research/fixtures.py']
    return {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in paths}


def old_module():
    data = subprocess.check_output(['git', 'show', BASELINE +
        ':Topology/UnknotRecognition/fast/fastunknot/normal_surface_orbits.py'], cwd=ROOT)
    module = types.ModuleType('fastunknot._normal_certificate_baseline')
    module.__package__ = 'fastunknot'
    exec(compile(data, BASELINE + ':normal_surface_orbits.py', 'exec'), module.__dict__)
    return module, digest(data)


def audit():
    import regina
    package = types.ModuleType('_report47_normal_audit')
    package.__path__ = [str(ARCHIVE)]
    sys.modules[package.__name__] = package
    reference = importlib.import_module(package.__name__ + '.normal_components')
    old, old_hash = old_module()
    rng = random.Random(SEED)
    rows = []
    for size in range(1, 9):
        raw, _ = layered_torus(size)
        tri = regina_triangulation(raw)
        base = [export_surface(s) for s in regina.NormalSurfaces(tri, regina.NS_STANDARD)]
        vectors = list(base) + [[[0] * 7 for _ in range(size)]]
        for _ in range(30):
            a, b = rng.choice(base), rng.choice(base)
            if any(sum(bool(x or y) for x, y in zip(u[4:], v[4:])) > 1
                   for u, v in zip(a, b)):
                continue
            x, y = rng.randrange(1, 4), rng.randrange(1, 4)
            vectors.append([[x * u + y * v for u, v in zip(a_row, b_row)]
                            for a_row, b_row in zip(a, b)])
        for vector in vectors:
            actual = normal_surface_topology(raw, vector, record_certificate=True)
            proof = actual['certificate']
            assert verify_normal_surface_certificate(raw, vector, proof)
            assert {k: v for k, v in actual.items() if k != 'certificate'} == old.normal_surface_topology(raw, vector)
            report = reference.analyze_normal_surface(raw, vector, record_trace=True)
            assert reference.verify_normal_surface_certificate(raw, vector, report['certificate'])
            summary = report['summary']
            native = regina_surface(tri, vector)
            parts = native.components()
            expected = dict(components=len(parts),
                orientable_components=sum(s.isOrientable() for s in parts),
                nonorientable_components=sum(not s.isOrientable() for s in parts),
                boundary_components=native.countBoundaries(),
                euler_characteristic=int(str(native.eulerChar())),
                compressing_disk=native.isCompressingDisc())
            for key, value in expected.items():
                assert actual[key] == value, (size, vector, key, value, actual[key])
                report_key = 'certifies_compressing_disk' if key == 'compressing_disk' else key
                assert summary[report_key] == value, (size, vector, report_key)
            rows.append(dict(tetrahedra=size, coordinates=vector, topology=proof['topology'],
                certificate_sha256=digest(json.dumps(json_safe(proof), sort_keys=True).encode())))
    raw, meridian = layered_torus(1)
    for caps in range(1, 5):
        raw, meridian = boundary_cap(raw, meridian)
        prepared = _prepare(raw, lambda: None)
        vectors = [meridian]
        for root in sorted(set(prepared['vertex_roots'])):
            vectors.append([[int(prepared['vertex_roots'][4*t+v] == root)
                             for v in range(4)] + [0]*3 for t in range(len(meridian))])
        for vector in vectors:
            actual = normal_surface_topology(raw, vector, record_certificate=True)
            proof = actual['certificate']
            assert verify_normal_surface_certificate(raw, vector, proof)
            assert {k: v for k, v in actual.items() if k != 'certificate'} == old.normal_surface_topology(raw, vector)
            report = reference.analyze_normal_surface(raw, vector, record_trace=True)
            assert reference.verify_normal_surface_certificate(raw, vector, report['certificate'])
            native = regina_surface(regina_triangulation(raw), vector)
            assert actual['components'] == report['summary']['components'] == len(native.components()) == 1
            assert actual['boundary_components'] == report['summary']['boundary_components'] == native.countBoundaries() == 1
            assert actual['euler_characteristic'] == report['summary']['euler_characteristic'] == int(str(native.eulerChar())) == 1
            assert actual['compressing_disk'] == report['summary']['certifies_compressing_disk'] == native.isCompressingDisc()
            assert actual['orientable_components'] == report['summary']['orientable_components'] == int(native.isOrientable()) == 1
            rows.append(dict(tetrahedra=len(vector), boundary_caps=caps, coordinates=vector,
                topology=proof['topology'], boundary_homology=proof['boundary_homology'],
                certificate_sha256=digest(json.dumps(json_safe(proof), sort_keys=True).encode())))
    archive_hashes = {name: digest((ARCHIVE/name).read_bytes()) for name in
                     ('normal_components.py', 'normal_interval_extraction.py',
                      'interval_orbits.py', 'interval_orbit_verify.py', 'integer_codec.py')}
    return dict(cases=rows, comparisons=len(rows), baseline_sha256=old_hash,
                report47_source_sha256=archive_hashes,
                counts=dict(compressing_disks=sum(r['topology']['compressing_disk'] for r in rows),
                    with_nonorientable_components=sum(r['topology']['nonorientable_components'] > 0 for r in rows),
                    disconnected=sum(r['topology']['components'] > 1 for r in rows)))


def benchmark():
    old, old_hash = old_module()
    rng = random.Random(SEED + 1)
    cases = [('meridian' + str(t), *layered_torus(t), 10 if t <= 8 else 1)
             for t in (1, 8, 32, 96)]
    tri, vector = layered_torus(8)
    cases.append(('parallel5000', tri, [[v * (1 << 5000) for v in row] for row in vector], 1))
    tri, _ = layered_torus(1)
    cases.append(('one_sided20000', tri, [[0, 0, 0, 0, 0, (1 << 20000) + 1, 0]], 5))
    rows = []
    for name, tri, vector, batch in cases:
        expected = old.normal_surface_topology(tri, vector)
        recorded = normal_surface_topology(tri, vector, record_certificate=True)
        proof = recorded['certificate']
        assert verify_normal_surface_certificate(tri, vector, proof)
        arms = ('old', 'current', 'current_AA', 'record', 'certified', 'replay')
        # Only computation is timed; equality assertions run outside each call.
        def call(arm):
            if arm in ('old', 'current', 'current_AA'):
                result = (old.normal_surface_topology(tri, vector) if arm == 'old'
                          else normal_surface_topology(tri, vector))
            elif arm in ('record', 'certified'):
                result = normal_surface_topology(tri, vector, record_certificate=True)
                if arm == 'certified' and not verify_normal_surface_certificate(tri, vector, result['certificate']):
                    raise AssertionError('replay failed')
            else:
                result = verify_normal_surface_certificate(tri, vector, proof)
            return result
        measured, warmups = [], []
        for round_id in range(-1, 5):
            order = list(arms); rng.shuffle(order)
            times = {}
            for arm in order:
                start = time.perf_counter()
                for _ in range(batch):
                    result = call(arm)
                times[arm] = (time.perf_counter() - start) / batch
                if arm == 'replay': assert result is True
                else:
                    if 'certificate' in result: assert result.pop('certificate') == proof
                    assert result == expected
            (warmups if round_id < 0 else measured).append(dict(order=order, seconds=times))
        medians = {arm: statistics.median(r['seconds'][arm] for r in measured) for arm in arms}
        ratios = {arm: statistics.median(r['seconds']['current']/r['seconds'][arm] for r in measured)
                  for arm in ('current_AA', 'old', 'record', 'certified', 'replay')}
        row = dict(name=name, tetrahedra=len(vector), coordinate_bits=max(v.bit_length() for r in vector for v in r),
                   batch=batch, warmups=warmups, samples=measured, medians=medians, current_over=ratios,
                   topology=proof['topology'], orbit_cycles=expected['cycles'],
                   proof_bytes=len(json.dumps(json_safe(proof), separators=(',', ':')).encode()),
                   orbit_events=sum(len(p['operations']) for p in proof['queries'].values()), certificate=proof)
        rows.append(row)
        print(name, json.dumps(dict(medians=medians, current_over=ratios)), flush=True)
    return dict(cases=rows, baseline_sha256=old_hash, rounds=5, excluded_warmups=1,
                scope='Fresh native manifold/coordinate validation and topology in old/current/record/certified; certified includes independent replay. Replay consumes a supplied proof and freshly reconstructs its source geometry. It is verification-only, not discovery speedup.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'benchmark'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    before = sources(); start = time.perf_counter()
    result = (audit if args.mode == 'audit' else benchmark)()
    assert before == sources()
    result.update(mode=args.mode, seed=SEED if args.mode == 'audit' else SEED+1,
                  baseline_commit=BASELINE, seconds=time.perf_counter()-start,
                  python=platform.python_version(), platform=platform.platform(),
                  source_sha256=before, source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('cases', 'source_sha256')}, indent=2))


if __name__ == '__main__':
    main()
