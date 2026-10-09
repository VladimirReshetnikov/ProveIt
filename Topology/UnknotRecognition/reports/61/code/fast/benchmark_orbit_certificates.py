"""Measure native certificate costs and marked-union reuse with paired controls."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
import time
import types

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.interval_incidence import (
    _prepare, _selected_union, _cone_rows,
    analyze_port_incidence, verify_port_incidence_certificate,
)
from fastunknot.normal_surface_orbits import normal_arc_pairings
from normal_orbit_research.fixtures import layered_torus

BASELINE = '8cd6dcfcda2788117413714c2c314489522ea42d'
ROOT = Path(__file__).resolve().parent


def old_kernel():
    source = subprocess.check_output(['git', 'show', BASELINE +
        ':Topology/UnknotRecognition/fast/fastunknot/interval_orbits.py'])
    module = types.ModuleType('_orbit_before_certificates')
    sys.modules[module.__name__] = module
    exec(compile(source, BASELINE + '/interval_orbits.py', 'exec'), module.__dict__)
    return module, hashlib.sha256(source).hexdigest()


def uncached(size, pairs, ports):
    """Same maintained kernel and coning, with one fresh query per nonempty mask.

    This ablation isolates union reuse from changes to the kernel. Like the
    report's original policy it has no cross-mask cache; it is a benchmark arm.
    """
    size, ports = _prepare(size, ports, 12, lambda: None)
    base = count_orbits(size, pairs)
    touched = [0] * (1 << len(ports))
    queries = 1
    for mask in range(1, len(touched)):
        union = _selected_union(ports, mask)
        if union:
            extra = [IntervalPairing(a, b, c, d) for a, b, c, d, _ in _cone_rows(union)]
            touched[mask] = base.orbits - count_orbits(size, pairs + extra).orbits + 1
            queries += 1
    full = len(touched) - 1
    histogram = [base.orbits - touched[full ^ mask] for mask in range(len(touched))]
    for bit in range(len(ports)):
        for mask in range(len(touched)):
            if mask & (1 << bit):
                histogram[mask] -= histogram[mask ^ (1 << bit)]
    return histogram, queries


def measure(arms, expected, rng, rounds, batch=1):
    samples = {arm: [] for arm in arms}
    orders = []
    for trial in range(-1, rounds):
        order = list(arms)
        rng.shuffle(order)
        orders.append(order)
        for arm in order:
            start = time.perf_counter_ns()
            for _ in range(batch):
                answer = arms[arm]()
            elapsed = (time.perf_counter_ns() - start) / (1e9 * batch)
            assert answer == expected, arm
            if trial >= 0:
                samples[arm].append(elapsed)
    return dict(seconds=samples, medians={a: median(v) for a, v in samples.items()},
                orders=orders, batch=batch,
                paired_ratio={a: median(x/y for x, y in zip(samples[next(iter(arms))], v))
                              for a, v in samples.items()})


def sources():
    names = ['benchmark_orbit_certificates.py', 'fastunknot/interval_orbits.py',
             'fastunknot/interval_orbit_verify.py', 'fastunknot/interval_incidence.py',
             'fastunknot/normal_surface_orbits.py', 'fastunknot/integer_codec.py',
             'normal_orbit_research/fixtures.py']
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    before = sources()
    baseline, old_hash = old_kernel()
    rng = random.Random(261008483)
    data = dict(schema='orbit_certificate_benchmark_v1', seed=261008483,
                python=platform.python_version(), platform=platform.platform(),
                baseline_commit=BASELINE, baseline_source_sha256=old_hash,
                checkout=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                rounds=args.rounds, warmups=1, counts=[], incidence=[],
                scope='Supplied interval and normal-arc queries; no whole-knot timings.')
    n = (1 << 4000) + 1
    p = (1 << 512) + 1
    tri, coords = layered_torus(32)
    normal_n, normal_pairs = normal_arc_pairings(tri, coords)
    cases = [('huge_translation', n, [IntervalPairing(0, n-2, 1, n-1)]),
             ('huge_reflection', n, [IntervalPairing(0, n-1, 0, n-1, True)]),
             ('chain64', 65*p, [IntervalPairing(i*p, (i+1)*p-1, (i+1)*p, (i+2)*p-1)
                                for i in range(64)]),
             ('normal32', normal_n, normal_pairs)]
    for name, size, pairs in cases:
        old_pairs = [baseline.IntervalPairing(p.a, p.b, p.c, p.d, p.reverse) for p in pairs]
        expected = baseline.count_orbits(size, old_pairs).orbits
        def traced(replay=False):
            result = count_orbits(size, pairs, record_certificate=True)
            if replay:
                assert verify_orbit_certificate(size, pairs, result.certificate)
            return result.orbits
        arms = dict(old=lambda: baseline.count_orbits(size, old_pairs).orbits,
                    current=lambda: count_orbits(size, pairs).orbits,
                    current_AA=lambda: count_orbits(size, pairs).orbits,
                    trace=traced, trace_replay=lambda: traced(True))
        row = measure(arms, expected, rng, args.rounds, batch=20 if name.startswith('huge') else 1)
        proof = count_orbits(size, pairs, record_certificate=True).certificate
        row.update(name=name, size_bits=size.bit_length(), pairings=len(pairs),
                   certificate_bytes=len(json.dumps(json_safe(proof)).encode()),
                   operations=len(proof['operations']))
        data['counts'].append(row)
    tri, coords = layered_torus(8)
    native_n, native_pairs = normal_arc_pairings(tri, coords)
    native_large_n, native_large_pairs = normal_arc_pairings(tri,
        [[(1 << 500)*v for v in row] for row in coords])
    cases = []
    for name, size, pairs, r in [('static', 1 << 4000, [], 8),
                               ('normal8', native_n, native_pairs, 6),
                               ('parallel500', native_large_n, native_large_pairs, 6)]:
        for shape in ('coincident', 'nested', 'disjoint'):
            ports = [[(0, size//2)] for _ in range(r)] if shape == 'coincident' else (
                [[(0, (i+1)*size//r)] for i in range(r)] if shape == 'nested' else
                [[(i*size//r, (i+1)*size//r)] for i in range(r)])
            cases.append((name+'_'+shape, size, pairs, ports))
    for name, size, pairs, ports in cases:
        expected, old_queries = uncached(size, pairs, ports)
        def certified():
            result = analyze_port_incidence(size, pairs, ports, record_certificate=True)
            assert verify_port_incidence_certificate(size, pairs, ports, result['certificate'])
            return result['histogram']
        arms = dict(uncached=lambda: uncached(size, pairs, ports)[0],
                    cached=lambda: analyze_port_incidence(size, pairs, ports)['histogram'],
                    cached_AA=lambda: analyze_port_incidence(size, pairs, ports)['histogram'],
                    certified=certified)
        row = measure(arms, expected, rng, args.rounds)
        result = analyze_port_incidence(size, pairs, ports, record_certificate=True)
        row.update(name=name, size_bits=size.bit_length(), pairings=len(pairs), ports=len(ports),
                   old_queries=old_queries, stats=result['stats'],
                   certificate_bytes=len(json.dumps(json_safe(result['certificate'])).encode()),
                   proof_count=len(result['certificate']['proofs']),
                   histogram_sha256=hashlib.sha256(json.dumps(json_safe(expected)).encode()).hexdigest())
        data['incidence'].append(row)
        print(name, old_queries, '->', row['stats']['orbit_queries'], flush=True)
    assert before == sources(), 'measured source changed during benchmark'
    data.update(source_sha256=before, source_sha256_after=sources(), measured_sources_unchanged=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+'\n')


if __name__ == '__main__':
    main()
