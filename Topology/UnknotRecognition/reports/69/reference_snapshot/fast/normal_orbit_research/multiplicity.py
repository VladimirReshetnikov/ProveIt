"""Independent scaling audit and paired common-multiplicity benchmarks."""
import argparse
import hashlib
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
from fastunknot.normal_surface_geometry import _TOPOLOGY_FIELDS
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from normal_orbit_research.fixtures import (
    layered_torus, boundary_cap, regina_triangulation, regina_surface,
)

BASELINE = 'a3f10a6637bba2e89e99a24113ec6bb8fd1f6614'
SEED = 261008497
AUDIT_INPUT = ROOT.parent/'synthesis/data/normal-certificate-native-audit.json'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sources():
    paths = [ROOT/'fastunknot'/name for name in (
        'normal_surface_orbits.py', 'normal_surface_geometry.py', 'normal_surface_verify.py',
        'normal_surface_parity.py', 'interval_orbits.py', 'interval_orbit_verify.py', 'integer_codec.py')]
    paths += [ROOT/'normal_orbit_research/fixtures.py', Path(__file__).resolve(), AUDIT_INPUT]
    return {str(p.relative_to(ROOT.parent)): digest(p.read_bytes()) for p in paths}


def pinned():
    modules, hashes = [], {}
    for name in ('normal_surface_orbits', 'normal_surface_verify'):
        data = subprocess.check_output(['git', 'show', BASELINE +
            ':Topology/UnknotRecognition/fast/fastunknot/' + name + '.py'], cwd=ROOT)
        module = types.ModuleType('fastunknot._multiplicity_old_' + name)
        module.__package__ = 'fastunknot'
        exec(compile(data, BASELINE + ':' + name, 'exec'), module.__dict__)
        modules.append(module); hashes[name] = digest(data)
    return *modules, hashes


def topology(result):
    return {key: result[key] for key in _TOPOLOGY_FIELDS if key in result}


def proof_bytes(proof):
    return len(json.dumps(json_safe(proof), separators=(',', ':')).encode())


def audit():
    old, old_check, hashes = pinned()
    inputs = json.loads(AUDIT_INPUT.read_text())['cases']
    rows = []
    for index, source in enumerate(inputs):
        raw, meridian = layered_torus(1 if source.get('boundary_caps') else source['tetrahedra'])
        for _ in range(source.get('boundary_caps', 0)):
            raw, meridian = boundary_cap(raw, meridian)
        tri = regina_triangulation(raw)
        for scale in (1, 2, 3, 4, 7):
            vector = [[scale * value for value in row] for row in source['coordinates']]
            before = old.normal_surface_topology(raw, vector, record_certificate=True)
            after = normal_surface_topology(raw, vector, record_certificate=True)
            assert topology(before) == topology(after)
            assert verify_normal_surface_certificate(raw, vector, before['certificate'])
            assert verify_normal_surface_certificate(raw, vector, after['certificate'])
            assert old_check.verify_normal_surface_certificate(raw, vector, before['certificate'])
            if after['certificate']['schema'] == 'normal-surface-topology-v1':
                assert old_check.verify_normal_surface_certificate(raw, vector, after['certificate'])
            native = regina_surface(tri, vector)
            parts = native.components()
            expected = dict(components=len(parts),
                orientable_components=sum(s.isOrientable() for s in parts),
                nonorientable_components=sum(not s.isOrientable() for s in parts),
                boundary_components=native.countBoundaries(),
                euler_characteristic=int(str(native.eulerChar())),
                compressing_disk=native.isCompressingDisc())
            assert all(after[k] == value for k, value in expected.items())
            rows.append(dict(input_index=index, scale=scale, divisor=after.get('coordinate_divisor', 1),
                topology=topology(after), old_cycles=before['cycles'], new_cycles=after['cycles'],
                old_proof_bytes=proof_bytes(before['certificate']), new_proof_bytes=proof_bytes(after['certificate'])))
    return dict(cases=rows, comparisons=len(rows), reduced=sum(r['divisor']>1 for r in rows),
                one_sided_cases=sum(r['topology']['nonorientable_components']>0 for r in rows),
                baseline_source_sha256=hashes,
                input_manifest=str(AUDIT_INPUT.relative_to(ROOT.parent)),
                counts_scope='original input topology; query statistics refer to the quotient when reduced')


def benchmark():
    old, old_check, hashes = pinned()
    rng = random.Random(SEED + 1)
    cases = [('primitive' + str(t), *layered_torus(t), batch)
             for t, batch in ((1, 20), (8, 5), (32, 1), (96, 1))]
    tri, vector = layered_torus(8)
    for bits in (5000, 20000):
        cases.append(('parallel' + str(bits), tri,
                      [[value * (1 << bits) for value in row] for row in vector], 1))
    tri, _ = layered_torus(1)
    factor = (1 << 20000) + 1
    cases += [('one_sided20000', tri, [[0, 0, 0, 0, 0, factor, 0]], 5),
              ('mixed20000', tri, [[factor, factor, factor, factor, 0, factor, 0]], 5)]
    rows = []
    arms = ('old', 'unreduced', 'current', 'current_AA', 'old_certified',
            'current_certified', 'old_replay', 'current_replay')
    for name, tri, vector, batch in cases:
        before = old.normal_surface_topology(tri, vector, record_certificate=True)
        after = normal_surface_topology(tri, vector, record_certificate=True)
        expected = topology(before)
        assert expected == topology(after)
        old_proof, new_proof = before['certificate'], after['certificate']
        assert old_check.verify_normal_surface_certificate(tri, vector, old_proof)
        assert verify_normal_surface_certificate(tri, vector, new_proof)
        def call(arm):
            if arm == 'old': return old.normal_surface_topology(tri, vector)
            if arm == 'unreduced': return normal_surface_topology(tri, vector, reduce_multiplicity=False)
            if arm in ('current', 'current_AA'): return normal_surface_topology(tri, vector)
            if arm == 'old_replay': return old_check.verify_normal_surface_certificate(tri, vector, old_proof)
            if arm == 'current_replay': return verify_normal_surface_certificate(tri, vector, new_proof)
            if arm == 'old_certified':
                result = old.normal_surface_topology(tri, vector, record_certificate=True)
                assert old_check.verify_normal_surface_certificate(tri, vector, result['certificate'])
                return result
            result = normal_surface_topology(tri, vector, record_certificate=True)
            assert verify_normal_surface_certificate(tri, vector, result['certificate'])
            return result
        warmups, samples = [], []
        for round_id in range(-1, 5):
            order = list(arms); rng.shuffle(order)
            times = {}
            for arm in order:
                start = time.perf_counter()
                for _ in range(batch): result = call(arm)
                times[arm] = (time.perf_counter() - start) / batch
                if arm.endswith('_replay'): assert result is True
                else:
                    assert topology(result) == expected
                    if 'certificate' in result:
                        assert result['certificate'] == (old_proof if arm == 'old_certified' else new_proof)
            (warmups if round_id < 0 else samples).append(dict(order=order, seconds=times))
        medians = {arm: statistics.median(r['seconds'][arm] for r in samples) for arm in arms}
        ratios = {label: statistics.median(r['seconds'][a]/r['seconds'][b] for r in samples)
                  for label, a, b in [('count', 'old', 'current'),
                    ('certified', 'old_certified', 'current_certified'),
                    ('replay', 'old_replay', 'current_replay'),
                    ('current_AA', 'current', 'current_AA'), ('old_unreduced', 'old', 'unreduced')]}
        row = dict(name=name, tetrahedra=len(vector), input_bits=before['maximum_coordinate_bits'],
                   divisor=after.get('coordinate_divisor', 1), batch=batch, medians=medians,
                   paired_ratios=ratios, samples=samples, warmups=warmups,
                   old_proof_bytes=proof_bytes(old_proof), new_proof_bytes=proof_bytes(new_proof),
                   old_certificate=old_proof, new_certificate=new_proof,
                   old_queries=before['queries'], new_queries=after['queries'])
        rows.append(row)
        print(name, json.dumps(dict(medians=medians, paired_ratios=ratios)), flush=True)
    return dict(cases=rows, baseline_source_sha256=hashes, rounds=5, excluded_warmups=1,
                scope='Every count/certified arm includes fresh manifold and coordinate validation; certified includes production and independent replay. Replay-only arms consume supplied proofs. Transport/serialization excluded. No source vector search or knot-diagram recognition is timed.')


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
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','source_sha256')},indent=2))


if __name__ == '__main__': main()
