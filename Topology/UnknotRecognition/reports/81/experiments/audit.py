"""Exact sector census against frozen full Regina enumeration, with fresh checks.

The declared selection repeats the preceding minimum-envelope audit: occupied
supports, all supports of size at most two, all sectors for t<=3, and 64 seeded
full sectors for each larger triangulation.  All selected d<=3 sectors are
checked, including the d=3 cases omitted by that predecessor.  Independent
dense/tie-interval replay runs on every d=3 sector and three lower-rank cases
per source.  No population or arbitrary-knot coverage inference is made.
"""

import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import platform
import random
import sys
import time

from fixtures import occupied, vector_key, ray_digest, fresh_standard, double_capped_fibonacci


def selected_supports(record):
    t = len(record['triangulation']['tetrahedra'])
    supports = {()}
    for field in ('standard_vertices', 'quad_vertices'):
        supports.update(occupied(s['coordinates']) for s in record[field])
    if t <= 3:
        supports.update(tuple((i, q) for i, q in enumerate(types) if q >= 0)
                        for types in product((-1, 0, 1, 2), repeat=t))
    else:
        for size in (1, 2):
            for indices in combinations(range(t), size):
                supports.update(tuple(zip(indices, types))
                                for types in product(range(3), repeat=size))
        rng = random.Random('sector-envelope-v1:' + record['id'])
        supports.update(tuple((i, rng.randrange(3)) for i in range(t)) for _ in range(64))
    return sorted(supports)


def run(args):
    sys.path.insert(0, str(args.fast.resolve()))
    from fastunknot.normal_sector import build_sector_kernel, sector_rays, _source_hash
    from fastunknot.sector_planar import sector_planar_rays, sector_planar_plan
    from fastunknot.sector_planar_verify import verify_planar_sector_certificate
    from fastunknot.sector_planar_certificate import discover_planar_in_sector
    from fastunknot.normal_sector_verify import verify_sector_witness
    from fastunknot.sector_planar_verify import verify_planar_exhaustion
    raw = args.corpus.read_bytes()
    corpus = json.loads(raw)
    counts, records = Counter(), []
    started = time.perf_counter()
    for source in corpus['records']:
        tri = source['triangulation']
        expected_all = [(set(occupied(s['coordinates'])), s['coordinates'])
                        for s in source['standard_vertices']]
        local, cases = Counter(), []
        for support in selected_supports(source):
            local['selected'] += 1
            kernel = build_sector_kernel(tri, support)
            d = len(kernel.basis)
            local[f'nullity_{d}'] += 1
            if d > 3:
                continue
            stats = {}
            actual = list(sector_planar_rays(kernel, stats=stats))
            expected = {vector_key(rows) for used, rows in expected_all
                        if used and used <= set(support)}
            assert {vector_key(rows) for rows in actual} == expected, (source['id'], support)
            plan = sector_planar_plan(kernel)
            if stats['section_dimension'] == 2:
                active = [len(g['cells']) - 1 for g in plan['groups']]
                bound = len(plan['domain']) + 2 * sum(active)
                bound += sum(a * b for a, b in combinations(active, 2))
                assert len(actual) <= bound
                local['planar_sections'] += 1
            local['audited'] += 1
            local['rays'] += len(actual)
            local[f'section_dimension_{stats["section_dimension"]}'] += 1
            independent = d == 3 or local['lowdim_replays'] < 3
            if independent:
                proof = dict(schema='normal-sector-planar-rays-v1',
                    source_sha256=_source_hash(tri), allowed_types=[list(s) for s in support],
                    quadrilateral_rays=sorted([rows[t][4 + q] for t, q in support]
                                             for rows in actual))
                assert verify_planar_sector_certificate(tri, proof), (source['id'], support)
                local['independent_replays'] += 1
                local['lowdim_replays'] += int(d < 3)
                if actual and local['mutations'] < 8:
                    for mode in ('omit', 'duplicate', 'scale', 'source'):
                        bad = deepcopy(proof)
                        if mode == 'omit':
                            bad['quadrilateral_rays'].pop()
                        elif mode == 'duplicate':
                            bad['quadrilateral_rays'].append(bad['quadrilateral_rays'][0])
                        elif mode == 'scale':
                            bad['quadrilateral_rays'][0] = [2*x for x in bad['quadrilateral_rays'][0]]
                        else:
                            bad['source_sha256'] = '0' * 64
                        assert not verify_planar_sector_certificate(tri, bad)
                        local['mutations'] += 1
            cases.append(dict(allowed_types=support, matching_nullity=d,
                              ray_count=len(actual), ray_sha256=ray_digest(actual),
                              independently_replayed=independent, stats=stats))
        if args.fresh_regina:
            regenerated = fresh_standard(tri)
            assert regenerated == {vector_key(s['coordinates']) for s in source['standard_vertices']}
            local['fresh_regina_enumerations'] += 1
        counts.update(local)
        records.append(dict(id=source['id'], counts=dict(local), cases=cases))
        print(source['id'], dict(local), flush=True)
    family = []
    for n in (1, 2, 4, 8):
        for types in product(range(3), repeat=2):
            example = double_capped_fibonacci(n, types)
            tri, support = example['triangulation'], example['allowed_types']
            kernel = build_sector_kernel(tri, support)
            assert len(kernel.basis) == 3
            rays = list(sector_planar_rays(kernel))
            old = list(sector_rays(kernel, method='arrangement'))
            assert {vector_key(r) for r in rays} == {vector_key(r) for r in old}
            if args.fresh_regina:
                full = fresh_standard(tri)
                selected = {flat for flat in full
                            if set(occupied([flat[i:i+7] for i in range(0,len(flat),7)]))
                            and set(occupied([flat[i:i+7] for i in range(0,len(flat),7)])) <= set(support)}
                assert selected == {vector_key(r) for r in rays}
                counts['fresh_family_regina'] += 1
            answer = discover_planar_in_sector(tri, support)
            valid = (verify_sector_witness(tri, answer['certificate'])
                     if answer['status'] == 'DISC_FOUND'
                     else verify_planar_exhaustion(tri, answer['certificate']))
            assert valid
            counts['family_discovery_replays'] += 1
            family.append(dict(id=example['id'], ray_count=len(rays),
                               ray_sha256=ray_digest(rays), status=answer['status']))
    result = dict(schema='planar-sector-audit-v1', baseline_commit=args.commit,
                  python=platform.python_version(), selection=__doc__,
                  corpus_sha256=sha256(raw).hexdigest(), counts=dict(counts),
                  records=records, families=family, seconds=time.perf_counter()-started)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('COMPLETE', result['counts'], 'seconds', result['seconds'], flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, default=Path(__file__).resolve().parents[1]
                        / 'fixtures/discovery_corpus.json')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--fresh-regina', action='store_true')
    parser.add_argument('--commit', default='8188525b70033dcfe7c51ea5ae2c8723ad0c0198')
    run(parser.parse_args())
