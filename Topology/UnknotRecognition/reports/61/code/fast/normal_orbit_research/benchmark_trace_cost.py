"""Batched follow-up for the noisy small count-only arms of the first run."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from benchmark_orbit_certificates import (
    BASELINE, IntervalPairing, count_orbits, layered_torus, measure,
    normal_arc_pairings, old_kernel, sources, verify_orbit_certificate,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    before = sources()
    before[str(Path(__file__).resolve().relative_to(ROOT))] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    baseline, old_hash = old_kernel()
    rng = random.Random(261008485)
    n, p = (1 << 4000) + 1, (1 << 512) + 1
    tri, coords = layered_torus(32)
    size, pairs = normal_arc_pairings(tri, coords)
    cases = [('huge_translation', n, [IntervalPairing(0, n-2, 1, n-1)], 1000),
             ('huge_reflection', n, [IntervalPairing(0, n-1, 0, n-1, True)], 1000),
             ('chain64', 65*p, [IntervalPairing(i*p, (i+1)*p-1, (i+1)*p, (i+2)*p-1)
                                for i in range(64)], 30),
             ('normal32', size, pairs, 10)]
    rows = []
    for name, size, pairs, batch in cases:
        old_pairs = [baseline.IntervalPairing(p.a, p.b, p.c, p.d, p.reverse) for p in pairs]
        def traced(replay=False):
            result = count_orbits(size, pairs, record_certificate=True)
            if replay:
                assert verify_orbit_certificate(size, pairs, result.certificate)
            return result.orbits
        arms = dict(old=lambda: baseline.count_orbits(size, old_pairs).orbits,
                    current=lambda: count_orbits(size, pairs).orbits,
                    current_AA=lambda: count_orbits(size, pairs).orbits,
                    trace=traced, trace_replay=lambda: traced(True))
        row = measure(arms, baseline.count_orbits(size, old_pairs).orbits,
                      rng, rounds=7, batch=batch)
        row['name'] = name
        rows.append(row)
        print(name, row['paired_ratio'], flush=True)
    after = sources()
    after[str(Path(__file__).resolve().relative_to(ROOT))] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    assert before == after
    result = dict(schema='orbit_trace_batched_followup_v1', seed=261008485,
                  baseline_commit=BASELINE, baseline_source_sha256=old_hash,
                  python=platform.python_version(), platform=platform.platform(),
                  rounds=7, warmups=1, counts=rows, source_sha256=before,
                  source_sha256_after=after, measured_sources_unchanged=True,
                  reason='Initial single-query timings had divergent identical controls; '
                         'retain original results and measure fresh batches of identical queries.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
