"""Compare all eligible selected sectors against frozen complete Regina rays.

For every one of the 48 frozen triangulations, select all supports occupied
by a listed standard or Q ray, every support of size at most two, and 64
fixed-seed full sectors.  On up to three tetrahedra, select every compatible
support.  The audit exhausts this declared finite selection and compares each
nullity-at-most-two query with the complete frozen standard-ray list filtered
by its allowed coordinates.  This is not a complete audit of all sectors on
the larger triangulations.  Optional fresh Regina runs rebuild selected full
standard-ray lists directly from the exact saved face pairings.
"""

import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import platform
import random
import time

from fastunknot.normal_sector import build_sector_kernel, sector_rays
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from fastunknot.sector_envelope import sector_envelope_rays, sector_envelope_plan
from .fixtures import capped_fibonacci, ray_digest, to_regina, vector_key


FAST = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = FAST.parent / 'reports/57/results/discovery_corpus.json'


def occupied(rows):
    return tuple((i, q) for i, row in enumerate(rows) for q in range(3) if row[4 + q])


def selected_supports(record):
    count = len(record['triangulation']['tetrahedra'])
    supports = {()}
    for field in ('standard_vertices', 'quad_vertices'):
        supports.update(occupied(surface['coordinates']) for surface in record[field])
    if count <= 3:
        supports.update(tuple((i, q) for i, q in enumerate(types) if q >= 0)
                        for types in product((-1, 0, 1, 2), repeat=count))
    else:
        for size in (1, 2):
            for indices in combinations(range(count), size):
                supports.update(tuple(zip(indices, types))
                                for types in product(range(3), repeat=size))
        rng = random.Random('sector-envelope-v1:' + record['id'])
        supports.update(tuple((i, rng.randrange(3)) for i in range(count))
                        for _ in range(64))
    return sorted(supports)


def fresh_standard(raw):
    import regina
    triangulation = to_regina(raw)
    surfaces = regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard)
    return {tuple(int(str(surface.triangles(i, vertex)))
                  if coordinate < 4 else int(str(surface.quads(i, coordinate - 4)))
                  for i in range(triangulation.size())
                  for coordinate, vertex in ((j, j) for j in range(7)))
            for surface in surfaces}


def run(corpus_path, fresh):
    data = corpus_path.read_bytes()
    corpus = json.loads(data)
    records = []
    all_counts = Counter()
    started = time.perf_counter()
    for source in corpus['records']:
        raw = source['triangulation']
        original = [(set(occupied(surface['coordinates'])), surface['coordinates'])
                    for surface in source['standard_vertices']]
        counts = Counter()
        cases = []
        for support in selected_supports(source):
            counts['selected'] += 1
            kernel = build_sector_kernel(raw, support)
            dimension = len(kernel.basis)
            counts['nullity_' + str(dimension)] += 1
            if dimension > 2:
                continue
            stats = {}
            actual = list(sector_envelope_rays(kernel, stats=stats))
            allowed = set(support)
            expected = [rows for positive, rows in original if positive and positive <= allowed]
            assert {vector_key(rows) for rows in actual} == {
                vector_key(rows) for rows in expected}, (source['id'], support)
            assert stats['bases_attempted'] == len(actual)
            counts['audited'] += 1
            counts['rays'] += len(actual)
            counts['interior_rays'] += stats['envelope_breakpoints']
            counts['empty_cones'] += not actual
            cases.append(dict(allowed_types=support, matching_nullity=dimension,
                              ray_count=len(actual), ray_sha256=ray_digest(actual), stats=stats))
        if fresh and source['id'] in ('fibonacci_lst_03', 'cap_1_2_1', 'cap_3_5_1',
                                      'interior_1_2', 'finite_trefoil',
                                      'solid_torus_sum_rp3'):
            regenerated = fresh_standard(raw)
            assert regenerated == {vector_key(surface['coordinates'])
                                   for surface in source['standard_vertices']}
            counts['fresh_regina_full_enumerations'] += 1
        all_counts.update(counts)
        records.append(dict(id=source['id'], counts=dict(counts), cases=cases))
        print(source['id'], dict(counts), flush=True)
    family = []
    family_fresh = 0
    for n in (1, 2, 4, 8, 16):
        for cap_type in (0, 1, 2):
            source = capped_fibonacci(n, cap_type)
            kernel = build_sector_kernel(source['triangulation'], source['allowed_types'])
            stats = {}
            rays = list(sector_envelope_rays(kernel, stats=stats))
            assert len(kernel.basis) == 2
            assert len(rays) == (2 if cap_type == 0 else 3)
            if fresh and n <= 4:
                allowed = set(source['allowed_types'])
                full = fresh_standard(source['triangulation'])
                filtered = set()
                for flat in full:
                    rows = [flat[7 * i:7 * i + 7] for i in range(n + 1)]
                    used = set(occupied(rows))
                    if used and used <= allowed:
                        filtered.add(flat)
                assert filtered == {vector_key(rows) for rows in rays}
                family_fresh += 1
            family.append(dict(base_tetrahedra=n, cap_type=cap_type,
                               ray_sha256=ray_digest(rays), stats=stats,
                               fresh_regina=bool(fresh and n <= 4)))
    example = capped_fibonacci(1, 1)
    kernel = build_sector_kernel(example['triangulation'], example['allowed_types'])
    standard = list(sector_envelope_rays(kernel))
    quad = list(sector_rays(kernel, phase='quadrilateral'))
    extra = [rows for rows in standard if rows not in quad]
    assert len(extra) == 1
    disk = normal_compressing_disk_count(example['triangulation'], extra[0],
                                       record_certificate=True)
    assert disk['compressing_disk_components'] == 1
    assert verify_normal_disk_count_certificate(example['triangulation'], extra[0],
                                                disk['certificate'])
    example.update(coordinates=extra[0], standard_rays=standard, quad_rays=quad,
                   disk_certificate=disk['certificate'])
    answer = dict(schema='sector-envelope-audit-v1', python=platform.python_version(),
                  corpus_sha256=sha256(data).hexdigest(), input_triangulations=len(records),
                  baseline_commit='66098968e88bba797143ac1bf7ad0ac4c5f697df',
                  source_sha256={name: sha256((FAST / name).read_bytes()).hexdigest()
                      for name in ('fastunknot/sector_envelope.py',
                                   'sector_envelope_research/audit.py',
                                   'sector_envelope_research/fixtures.py')},
                  selection=__doc__, counts=dict(all_counts), records=records,
                  capped_family=family, extra_disc_example=example,
                  fresh_regina_full_enumerations=(
                      all_counts['fresh_regina_full_enumerations'] + family_fresh),
                  seconds=time.perf_counter() - started)
    if fresh:
        import regina
        answer['regina_version'] = regina.versionString()
    return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--corpus', type=Path, default=DEFAULT_CORPUS)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--fresh-regina', action='store_true')
    args = parser.parse_args()
    answer = run(args.corpus, args.fresh_regina)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(answer, indent=2) + '\n')
    example = args.output.with_name('extra_non_q_disc.json')
    example.write_text(json.dumps(answer['extra_disc_example'], indent=2) + '\n')
    print('COMPLETE', answer['counts'], 'seconds', answer['seconds'], flush=True)


if __name__ == '__main__':
    main()
