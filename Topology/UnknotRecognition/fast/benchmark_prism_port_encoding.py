"""Complete vector/automatic port queries with independent replay and an A/A control."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot.integer_codec import json_safe
from fastunknot.normal_prism_interfaces import normal_prism_face_regions
from fastunknot.normal_prism_interfaces_verify import verify_normal_prism_interfaces
from normal_orbit_research.fixtures import layered_torus

FAST = Path(__file__).resolve().parent
REPO = FAST.parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cases = {}
    for t, copies in ((1, 1), (4, 1), (16, 1), (32, 1), (64, 1), (16, 1 << 500)):
        raw, vector = layered_torus(t)
        cases[f'layered_{t}_copies_bits_{copies.bit_length()}'] = (raw, [[copies*x for x in row] for row in vector])
    paths = [Path(__file__), FAST/'fastunknot/normal_prism_interfaces.py',
             FAST/'fastunknot/normal_prism_interfaces_verify.py', FAST/'fastunknot/weighted_orbits.py',
             FAST/'fastunknot/weighted_orbit_verify.py', FAST/'fastunknot/interval_orbits.py',
             FAST/'normal_orbit_research/fixtures.py']
    pins = {str(p.relative_to(REPO)): sha256(p.read_bytes()).hexdigest() for p in paths}
    arms = {'vector': 'vector', 'vector_control': 'vector', 'auto': 'auto'}
    rng = random.Random(26101103)
    samples, expected, details = [], {}, {}
    for round_number in range(6):
        tasks = [(name, arm) for name in cases for arm in arms]
        rng.shuffle(tasks)
        for name, arm in tasks:
            raw, rows = cases[name]
            start = perf_counter()
            answer = normal_prism_face_regions(raw, rows, record_certificate=True, port_encoding=arms[arm])
            assert verify_normal_prism_interfaces(raw, rows, answer['certificate'])
            wire = json.dumps(json_safe(answer), sort_keys=True, separators=(',', ':')).encode()
            elapsed = perf_counter() - start
            digest = sha256(json.dumps(json_safe(answer['structure']), sort_keys=True,
                                       separators=(',', ':')).encode()).hexdigest()
            assert expected.setdefault(name, digest) == digest, (name, arm)
            details[name] = dict(tetrahedra=len(rows), ports=len(answer['structure']['ports']),
                                 maximum_coordinate_bits=max(x.bit_length() for row in rows for x in row))
            samples.append(dict(case=name, arm=arm, round=round_number, warmup=round_number == 0,
                seconds=elapsed, structure_sha256=digest, result_bytes=len(wire),
                weight_dimension=answer['weight_dimension'], maximum_weight_runs=answer['stats']['maximum_weight_runs']))
        print('completed round', round_number, flush=True)
    for p in paths:
        assert sha256(p.read_bytes()).hexdigest() == pins[str(p.relative_to(REPO))]
    summary = {}
    for name in cases:
        rows = [r for r in samples if r['case'] == name and not r['warmup']]
        def paired(other):
            return statistics.median(next(r['seconds'] for r in rows if r['round'] == i and r['arm'] == 'vector') /
                                     next(r['seconds'] for r in rows if r['round'] == i and r['arm'] == other)
                                     for i in range(1, 6))
        summary[name] = dict(paired_vector_over_auto=paired('auto'), paired_identical_control=paired('vector_control'),
            median_seconds={arm: statistics.median(r['seconds'] for r in rows if r['arm'] == arm) for arm in arms},
            result_bytes={arm: next(r['result_bytes'] for r in rows if r['arm'] == arm) for arm in arms},
            weight_dimension={arm: next(r['weight_dimension'] for r in rows if r['arm'] == arm) for arm in arms})
    output = dict(python=platform.python_version(), seed=26101103, source_sha256=pins,
        timing='Fresh source validation, face clipping, orbit discovery, weighted transport, independent '
               'source/certificate replay and result serialization are all timed. Workload preparation '
               'and structure digest comparison are excluded. Five shuffled paired rounds plus one '
               'warmup and an identical vector control. Both encodings use the same linear contraction '
               'kernel. These are standalone geometry queries, not full recognizer timings.',
        details=details, summary=summary, samples=samples)
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
