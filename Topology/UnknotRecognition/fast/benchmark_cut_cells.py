"""Complete raw cut representations: binary CW with proof versus explicit Regina IsoSig."""
import argparse
import gc
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_cells import normal_cut_cell_complex
from fastunknot.normal_cut_cells_verify import verify_normal_cut_cell_complex
from normal_orbit_research.fixtures import layered_torus, regina_triangulation, regina_surface

FAST = Path(__file__).resolve().parent; REPO = FAST.parents[2]
def encode(value): return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def main():
    from regina import versionString
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
    cases = {}
    for t, copies in ((1, 0), (1, 1), (1, 16), (1, 128), (1, 1024), (1, 4096), (16, 1)):
        raw, base = layered_torus(t); cases[f'layered_{t}_copies_{copies}'] = raw, [[copies*x for x in row] for row in base]
    paths = [Path(__file__), FAST/'fastunknot/normal_cut_cells.py', FAST/'fastunknot/normal_cut_cells_verify.py',
             FAST/'fastunknot/normal_cut_boundary.py', FAST/'fastunknot/normal_cut_boundary_verify.py',
             FAST/'fastunknot/normal_surface_geometry.py', FAST/'fastunknot/integer_codec.py', FAST/'normal_orbit_research/fixtures.py']
    pins = {str(p.relative_to(REPO)): sha256(p.read_bytes()).hexdigest() for p in paths}
    rng = random.Random(26101133); samples = []; expected = {}; arms = ('regina', 'regina_control', 'native')
    for round_number in range(6):
        tasks = [(name, arm) for name in cases for arm in arms]; rng.shuffle(tasks)
        for name, arm in tasks:
            raw, rows = cases[name]; gc.collect(); start = perf_counter()
            if arm == 'native':
                answer = normal_cut_cell_complex(raw, rows, record_certificate=True)
                assert verify_normal_cut_cell_complex(raw, rows, answer['certificate'])
                wire = encode(answer); chi = answer['summary']['euler_characteristic']
                details = dict(result_bytes=len(wire), family_records=sum(len(answer['geometry'][k]) for k in ('vertices', 'edges', 'faces', 'chambers')),
                               physical_cells=sum(answer['geometry'][k+'_points'] for k in ('vertex', 'edge', 'face', 'chamber')))
                del answer
            else:
                cut = regina_surface(regina_triangulation(raw), rows).cutAlong()
                wire = encode(dict(triangulation_isosig=cut.isoSig())); chi = cut.eulerCharManifold()
                details = dict(result_bytes=len(wire), cut_tetrahedra=cut.size())
                del cut
            elapsed = perf_counter()-start
            assert expected.setdefault(name, chi) == chi
            samples.append(dict(case=name, arm=arm, round=round_number, warmup=round_number == 0, seconds=elapsed,
                                completed=True, euler_characteristic=chi, **details))
            del wire, details
        print('completed round', round_number, flush=True)
    for p in paths: assert sha256(p.read_bytes()).hexdigest() == pins[str(p.relative_to(REPO))]
    summary = {}
    for name in cases:
        rows = [r for r in samples if r['case'] == name and not r['warmup']]
        def paired(arm):
            return statistics.median(next(r['seconds'] for r in rows if r['arm'] == 'regina' and r['round'] == i) /
                                     next(r['seconds'] for r in rows if r['arm'] == arm and r['round'] == i) for i in range(1, 6))
        summary[name] = dict(paired_regina_over_native=paired('native'), identical_control=paired('regina_control'),
            median_seconds={arm: statistics.median(r['seconds'] for r in rows if r['arm'] == arm) for arm in arms},
            result_bytes={arm: next(r['result_bytes'] for r in rows if r['arm'] == arm) for arm in arms})
    result = dict(source_sha256=pins, python=platform.python_version(), regina_version=versionString(), seed=26101133,
        timing='Complete raw-cut representation task. Native constructs full source-labelled CW cells, independently checks its '
               'source proof and serializes the entire result, including source charts and coordinates. Regina builds its explicit '
               '3D cut and serializes its canonical triangulation IsoSig. Representations are of the same source cut but their '
               'formats and refinements differ. Euler equality is a timing-run check only; geometric, chain and homology validity '
               'are supplied by the separate source audit. Input preparation, prior-result cleanup, garbage collection and '
               'comparison are excluded. Five shuffled paired rounds plus a warmup and identical Regina control. No full-recognizer claim.',
        samples=samples, summary=summary)
    args.output.write_bytes(encode(result)+b'\n'); print(json.dumps(summary, indent=2))


if __name__ == '__main__': main()
