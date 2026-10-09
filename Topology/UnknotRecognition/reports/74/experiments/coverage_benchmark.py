"""Compare complete enumeration followed by independent coverage checking."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import statistics
import sys
import time


ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--code-root', type=Path, default=ROOT/'code')
    parser.add_argument('--output', type=Path, default=ROOT/'results/coverage.json')
    parser.add_argument('--sizes', nargs='+', type=int, default=[1, 8, 16])
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--capacity', nargs='*', type=int, default=[32, 64, 128])
    args = parser.parse_args()
    sys.path.insert(0, str(args.code_root.resolve()))
    from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays
    from fastunknot.sector_envelope_certificate import certify_sector_enumeration
    from fastunknot.sector_envelope_verify import verify_sector_envelope_certificate
    from fastunknot.integer_codec import json_safe
    from sector_envelope_research.benchmark import load_baseline
    from sector_envelope_research.fixtures import capped_fibonacci, ray_digest
    baseline = load_baseline()
    paths = ['fastunknot/normal_sector.py', 'fastunknot/normal_sector_verify.py',
             'fastunknot/sector_envelope.py', 'fastunknot/sector_envelope_certificate.py',
             'fastunknot/sector_envelope_verify.py',
             'sector_envelope_research/baseline_normal_sector.py']
    pins = {name: sha256((args.code_root/name).read_bytes()).hexdigest() for name in paths}
    pins['coverage_benchmark.py'] = sha256(Path(__file__).read_bytes()).hexdigest()
    result = dict(schema='sector-envelope-coverage-benchmark-v1',
        description=__doc__, python=platform.python_version(), platform=platform.platform(),
        repeats=args.repeats, source_sha256=pins, cases=[], capacity=[], certificates=[])
    started = time.perf_counter()
    for n in args.sizes:
        fixture = capped_fibonacci(n, 1)
        raw, allowed = fixture['triangulation'], fixture['allowed_types']
        reference = None

        def measure(arm):
            nonlocal reference
            begin = time.perf_counter_ns()
            if arm == 'old':
                kernel = baseline.build_sector_kernel(raw, allowed)
                rays = list(baseline.sector_rays(kernel, phase='standard',
                                               method='arrangement'))
                produced = time.perf_counter_ns()
                model = dense_sector_model(raw, allowed)
                expected = dense_reference_rays(model, 'standard')
                assert ray_digest(rays) == ray_digest(value[0] for value in expected.values())
                certificate = None
                stats = {}
            else:
                answer = certify_sector_enumeration(raw, allowed)
                assert answer['status'] == 'COMPLETE'
                rays, certificate = answer['coordinates'], answer['certificate']
                produced = time.perf_counter_ns()
                stats = {}
                assert verify_sector_envelope_certificate(raw, certificate, stats=stats)
            end = time.perf_counter_ns()
            digest = ray_digest(rays)
            if reference is None:
                reference = digest
            assert digest == reference
            wire = json.dumps(json_safe(certificate), separators=(',', ':')).encode()
            if arm == 'new':
                last_certificate[0] = certificate
            return dict(total_ns=end-begin, producer_ns=produced-begin,
                verifier_ns=end-produced, ray_sha256=digest, rays=len(rays),
                certificate_bytes=len(wire) if certificate is not None else None,
                verifier_stats=stats)

        last_certificate = [None]
        warmup = {arm: measure(arm) for arm in ('old', 'new')}
        rounds = []
        for j in range(args.repeats):
            order = ['old', 'new'] if j % 2 == 0 else ['new', 'old']
            arms = {arm: measure(arm) for arm in order}
            rounds.append(dict(round=j, order=order, arms=arms))
            print('PAIR', n, j, arms['old']['total_ns']/1e9,
                  arms['new']['total_ns']/1e9, flush=True)
        ratios = [r['arms']['old']['total_ns']/r['arms']['new']['total_ns'] for r in rounds]
        result['cases'].append(dict(base_tetrahedra=n, tetrahedra=n+1,
            warmup=warmup, rounds=rounds,
            old_median_ns=statistics.median(r['arms']['old']['total_ns'] for r in rounds),
            new_median_ns=statistics.median(r['arms']['new']['total_ns'] for r in rounds),
            paired_speedup_median=statistics.median(ratios),
            paired_speedup_min=min(ratios), paired_speedup_max=max(ratios)))
        result['certificates'].append(dict(fixture=fixture, certificate=last_certificate[0]))
    for n in args.capacity:
        fixture = capped_fibonacci(n, 1)
        raw, allowed = fixture['triangulation'], fixture['allowed_types']
        start = time.perf_counter_ns()
        answer = certify_sector_enumeration(raw, allowed)
        middle = time.perf_counter_ns()
        stats = {}
        assert verify_sector_envelope_certificate(raw, answer['certificate'], stats=stats)
        stop = time.perf_counter_ns()
        wire = json.dumps(json_safe(answer['certificate']), separators=(',', ':')).encode()
        result['capacity'].append(dict(base_tetrahedra=n, tetrahedra=n+1,
            total_ns=stop-start, producer_ns=middle-start, verifier_ns=stop-middle,
            certificate_bytes=len(wire), verifier_stats=stats,
            scope='new only; no comparative speedup'))
        result['certificates'].append(dict(fixture=fixture, certificate=answer['certificate']))
        print('CAPACITY', n, (stop-start)/1e9, flush=True)
    assert all(sha256((args.code_root/name).read_bytes()).hexdigest() == value
               for name, value in pins.items() if name != 'coverage_benchmark.py')
    result['seconds'] = time.perf_counter()-started
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2)+'\n')
    print('COMPLETE', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
