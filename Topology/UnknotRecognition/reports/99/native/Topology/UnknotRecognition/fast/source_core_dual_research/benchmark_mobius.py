"""Paired complete supplied-cut timings on an interior-vertex Mobius family.

Both methods start from the same four-tetrahedron source and normal vector.
Native totals include certificate production and independent replay.  Regina
totals include source conversion, actual cutting, component triangulation,
and exact handlebody recognition.  These are not whole knot-recognition times.
"""

import argparse
from collections import Counter
import csv
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

import regina

from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import interior_vertex_torus, regina_surface, regina_triangulation


def native(raw, rows):
    start = time.perf_counter()
    result = normal_cut_handlebodies(raw, rows, record_certificate=True)
    produced = time.perf_counter()
    assert result['status'] == 'COMPLETE'
    assert verify_normal_cut_handlebodies(raw, rows, result['certificate'])
    stopped = time.perf_counter()
    return result['census']['histogram'], dict(producer=produced-start,
        independent_replay=stopped-produced, total=stopped-start)


def explicit(raw, rows):
    start = time.perf_counter()
    triangulation = regina_triangulation(raw)
    surface = regina_surface(triangulation, rows)
    converted = time.perf_counter()
    cut = surface.cutAlong()
    cut_finished = time.perf_counter()
    pieces = list(cut.triangulateComponents())
    split = time.perf_counter()
    genera = Counter(p.recogniseHandlebody() for p in pieces)
    stopped = time.perf_counter()
    histogram = [dict(genus=g, multiplicity=n) for g, n in sorted(genera.items())]
    return histogram, dict(source_conversion=converted-start, cut=cut_finished-converted,
        component_triangulation=split-cut_finished, handlebody_recognition=stopped-split,
        total=stopped-start, expanded_tetrahedra=cut.size(), components=len(pieces))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        raise ValueError('rounds must be positive')
    args.output.mkdir(parents=True, exist_ok=True)
    raw, basis = interior_vertex_torus()
    rng = random.Random(20261012)
    output = dict(source_revision='8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4',
        python=sys.version, platform=platform.platform(), regina=regina.versionString(),
        rounds=args.rounds, random_seed=20261012, timer='perf_counter',
        scope='Supplied-cut complete query: native proof+replay versus Regina source conversion+cut+components+exact recognition.',
        cases=[])
    for copies in (1, 4, 16, 64, 256, 1024):
        rows = [[copies*v for v in row] for row in basis['mobius']]
        expected = [dict(genus=1, multiplicity=copies//2+1)]
        assert native(raw, rows)[0] == explicit(raw, rows)[0] == expected
        samples = []
        for _ in range(args.rounds):
            order = ['native', 'regina']
            rng.shuffle(order)
            sample = dict(order=order)
            for name in order:
                histogram, timing = (native if name == 'native' else explicit)(raw, rows)
                assert histogram == expected
                sample[name] = timing
            samples.append(sample)
        nmed = {key: statistics.median(x['native'][key] for x in samples)
                for key in samples[0]['native']}
        rmed = {key: statistics.median(x['regina'][key] for x in samples)
                for key in samples[0]['regina']}
        item = dict(copies=copies, source_tetrahedra=4, normal_disks=sum(map(sum, rows)),
            expected=expected, native_median=nmed, regina_median=rmed,
            median_paired_ratio=statistics.median(x['regina']['total']/x['native']['total']
                                                 for x in samples), samples=samples)
        output['cases'].append(item)
        print(json.dumps({k:v for k,v in item.items() if k!='samples'}), flush=True)
        (args.output/'mobius_benchmark.json').write_text(json.dumps(output, indent=2)+'\n')
    with (args.output/'mobius_benchmark.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['copies','normal_disks','components','expanded_tetrahedra',
            'native_producer_ms','native_replay_ms','native_total_ms','regina_conversion_ms',
            'regina_cut_ms','regina_components_ms','regina_recognition_ms','regina_total_ms',
            'median_paired_regina_over_native'])
        for item in output['cases']:
            n, r = item['native_median'], item['regina_median']
            writer.writerow([item['copies'],item['normal_disks'],r['components'],r['expanded_tetrahedra'],
                *[1000*n[k] for k in ('producer','independent_replay','total')],
                *[1000*r[k] for k in ('source_conversion','cut','component_triangulation',
                                     'handlebody_recognition','total')],item['median_paired_ratio']])


if __name__ == '__main__':
    main()
