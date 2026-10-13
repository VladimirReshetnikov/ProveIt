"""Complete cut-boundary profile queries, native source proof versus Regina cuts."""
import argparse
from collections import Counter
import gc
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot.normal_cut_boundary import normal_cut_boundary
from fastunknot.normal_cut_boundary_verify import verify_normal_cut_boundary
from fastunknot.integer_codec import json_safe
from normal_orbit_research.cut_boundary import native_profiles, regina_profiles
from normal_orbit_research.fixtures import layered_torus

FAST = Path(__file__).resolve().parent
REPO = FAST.parents[2]


def encode(value): return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()
def canonical(boundary, pieces):
    return dict(boundary=[list(k if isinstance(k, tuple) else (k,))+[v] for k, v in sorted(boundary.items())],
                pieces=[list(k)+[v] for k, v in sorted(pieces.items())])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
    cases = {}
    for t, copies in ((1, 0), (1, 1), (1, 16), (1, 128), (1, 1024), (1, 4096), (16, 1)):
        raw, rows = layered_torus(t); cases[f'layered_{t}_copies_{copies}'] = (raw, [[copies*x for x in row] for row in rows])
    paths = [Path(__file__), FAST/'fastunknot/normal_cut_boundary.py', FAST/'fastunknot/normal_cut_boundary_verify.py',
             FAST/'fastunknot/normal_surface_geometry.py', FAST/'fastunknot/normal_cut_complement.py',
             FAST/'fastunknot/normal_cut_complement_verify.py', FAST/'fastunknot/orbit_transversal.py',
             FAST/'fastunknot/orbit_transversal_verify.py', FAST/'fastunknot/weighted_orbits.py',
             FAST/'fastunknot/weighted_orbit_verify.py', FAST/'fastunknot/interval_orbits.py',
             FAST/'normal_orbit_research/cut_boundary.py', FAST/'normal_orbit_research/fixtures.py']
    pins = {str(p.relative_to(REPO)): sha256(p.read_bytes()).hexdigest() for p in paths}
    from regina import versionString
    rng = random.Random(26101123); arms = ('regina', 'regina_control', 'native'); samples = []; expected = {}
    for round_number in range(6):
        tasks = [(name, arm) for name in cases for arm in arms]; rng.shuffle(tasks)
        for name, arm in tasks:
            raw, rows = cases[name]; gc.collect(); start = perf_counter()
            if arm == 'native':
                answer = normal_cut_boundary(raw, rows, record_certificate=True)
                assert verify_normal_cut_boundary(raw, rows, answer['certificate'])
                boundary, pieces = native_profiles(answer['summary'])
                wire = encode(answer); details = dict(complete=True, result_bytes=len(wire),
                    cell_face_families=len(answer['geometry']['faces']), cell_edge_families=len(answer['geometry']['edges']))
                del answer, wire
            else:
                boundary, pieces, tetrahedra = regina_profiles(raw, rows)
                details = dict(complete=True, cut_tetrahedra=tetrahedra)
            payload = encode(canonical(boundary, pieces)); elapsed = perf_counter()-start
            digest = sha256(payload).hexdigest(); assert expected.setdefault(name, digest) == digest
            samples.append(dict(case=name, arm=arm, round=round_number, warmup=round_number == 0,
                                seconds=elapsed, profile_sha256=digest, **details))
            del boundary, pieces, payload, details
        print('completed round', round_number, flush=True)
    for p in paths: assert sha256(p.read_bytes()).hexdigest() == pins[str(p.relative_to(REPO))]
    summary = {}
    for name in cases:
        records = [r for r in samples if r['case'] == name and not r['warmup']]
        def paired(arm):
            return statistics.median(next(r['seconds'] for r in records if r['arm'] == 'regina' and r['round'] == i) /
                                     next(r['seconds'] for r in records if r['arm'] == arm and r['round'] == i) for i in range(1, 6))
        summary[name] = dict(paired_regina_over_native=paired('native'), identical_control=paired('regina_control'),
            median_seconds={arm: statistics.median(r['seconds'] for r in records if r['arm'] == arm) for arm in arms})
    result = dict(source_sha256=pins, python=platform.python_version(), regina_version=versionString(), seed=26101123,
        timing='Common task: complete boundary genera and per-piece boundary count/total genus. '
               'All source construction, cutting/query work and common output serialization are timed. '
               'Native additionally constructs the full compressed boundary cells, independently replays '
               'their source-bound proof and serializes its complete result. Regina constructs its explicit '
               '3D cut and returns its profiles; its expanded triangulation is not serialized. '
               'This compares the common census task, not identical geometric outputs or whole recognition. '
               'Input preparation, prior-result cleanup, garbage collection and digest comparison are outside timing. '
               'Five shuffled paired rounds plus one warmup, with an identical Regina control.',
        samples=samples, summary=summary)
    args.output.write_bytes(encode(result)+b'\n'); print(json.dumps(summary, indent=2))


if __name__ == '__main__': main()
