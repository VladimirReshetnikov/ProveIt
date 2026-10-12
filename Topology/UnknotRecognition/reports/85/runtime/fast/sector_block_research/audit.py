"""Reproduce exact corpus checks and complete producer/replay measurements.

Run from fast/:
  python -m sector_block_research.audit audit --output path.json
  python -m sector_block_research.audit benchmark --output path.json --rounds 3
"""

import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
import random
from statistics import median
from time import perf_counter

from fastunknot.normal_sector import sector_rays
from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.integer_codec import json_safe
from fastunknot.sector_blocks import certify_sector_block_rays, screen_sector_blocks
from fastunknot.sector_blocks_verify import verify_block_euler, verify_block_ray_certificate
from fastunknot.sector_sparse import PreparedSectorSource
from .fixtures import capped_bipyramid_chain


def _ray_key(rows):
    return tuple(value for row in rows for value in row)


def _digest(rays):
    wire = json.dumps(sorted(_ray_key(rows) for rows in rays), separators=(',', ':')).encode()
    return sha256(wire).hexdigest()


def _supports(record):
    size = len(record['triangulation']['tetrahedra'])
    supports = {()}
    for field in ('standard_vertices', 'quad_vertices'):
        supports.update(tuple((i, typ) for i, row in enumerate(surface['coordinates'])
                              for typ in range(3) if row[4 + typ])
                        for surface in record[field])
    if size <= 3:
        supports.update(tuple((i, typ) for i, typ in enumerate(types) if typ >= 0)
                        for types in product((-1, 0, 1, 2), repeat=size))
    else:
        for active in (1, 2):
            for indices in combinations(range(size), active):
                supports.update(tuple(zip(indices, types)) for types in product(range(3), repeat=active))
        rng = random.Random('sector-envelope-v1:' + record['id'])
        supports.update(tuple((i, rng.randrange(3)) for i in range(size)) for _ in range(64))
    return sorted(supports)


def audit():
    bank = Path(__file__).resolve().parents[2] / 'reports/57/results/discovery_corpus.json'
    records = json.loads(bank.read_text())['records']
    cases, statuses = [], Counter()
    for record in records:
        raw = record['triangulation']
        source = PreparedSectorSource(raw)
        for support in _supports(record):
            kernel = source.build(support)
            if len(kernel.basis) <= 3:
                continue
            old_stats = {}
            old = list(sector_rays(kernel, phase='quadrilateral', stats=old_stats))
            result = certify_sector_block_rays(raw, support)
            assert result['status'] == 'COMPLETE'
            assert _digest(old) == _digest(result['rays'])
            assert verify_block_ray_certificate(raw, result['certificate'])
            screen = screen_sector_blocks(raw, support)
            assert screen['status'] in ('POSITIVE_EULER', 'NO_POSITIVE_EULER')
            assert verify_block_euler(raw, screen['certificate'])
            expected = any(_coordinates(source.prepared, rows, lambda: None)
                           ['euler_characteristic'] > 0 for rows in old)
            archival = [surface['coordinates'] for surface in record['standard_vertices']
                        if any(row[4 + typ] for row in surface['coordinates'] for typ in range(3))
                        and all(not row[4 + typ] or (i, typ) in support
                                for i, row in enumerate(surface['coordinates']) for typ in range(3))]
            archival_positive = any(_coordinates(source.prepared, rows, lambda: None)
                                    ['euler_characteristic'] > 0 for rows in archival)
            assert expected == archival_positive == (screen['status'] == 'POSITIVE_EULER')
            statuses[screen['status']] += 1
            cases.append(dict(source=record['id'], allowed_types=support,
                raw_nullity=len(kernel.basis), block_nullities=result['stats']['block_nullities'],
                original_candidates=old_stats['bases_attempted'],
                block_candidates=result['stats']['bases_attempted'], rays=len(old),
                ray_sha256=_digest(old), euler_status=screen['status']))
    assert len(cases) == 188
    return dict(scope='Complete high-nullity supplied sectors from the retained source corpus.',
        cases=cases, summary=dict(cases=len(cases), statuses=dict(statuses),
            split_sectors=sum(len(case['block_nullities']) > 1 for case in cases),
            reduced_candidates=sum(case['block_candidates'] < case['original_candidates'] for case in cases),
            original_candidates=sum(case['original_candidates'] for case in cases),
            block_candidates=sum(case['block_candidates'] for case in cases),
            max_candidate_factor=max(case['original_candidates'] / case['block_candidates']
                                     for case in cases if case['block_candidates']),
            all_ray_sets_equal=True, all_independent_certificates_accepted=True,
            all_euler_decisions_equal_archived_standard_oracle=True))


def _old_complete(raw, support):
    source = PreparedSectorSource(raw)
    kernel = source.build(support)
    stats = {}
    rays = list(sector_rays(kernel, phase='quadrilateral', stats=stats))
    model = dense_sector_model(raw, support)
    reference = dense_reference_rays(model, 'quadrilateral')
    assert {_ray_key(rows) for rows in rays} == {_ray_key(rows) for rows, _ in reference.values()}
    return dict(ray_sha256=_digest(rays), rays=len(rays), candidates=stats['bases_attempted'])


def _new_complete(raw, support):
    result = certify_sector_block_rays(raw, support)
    assert result['status'] == 'COMPLETE'
    assert verify_block_ray_certificate(raw, result['certificate'])
    wire = json.dumps(json_safe(result['certificate']), sort_keys=True, separators=(',', ':')).encode()
    return dict(ray_sha256=_digest(result['rays']), rays=len(result['rays']),
                candidates=result['stats']['bases_attempted'], certificate_bytes=len(wire))


def benchmark(rounds, max_balls):
    if rounds < 1 or max_balls < 1:
        raise ValueError('rounds and max_balls must be positive')
    cases = []
    for balls in range(1, max_balls + 1):
        fixture = capped_bipyramid_chain(balls)
        raw, support = fixture['triangulation'], fixture['allowed_types']
        records = []
        for round_number in range(rounds):
            order = ('old', 'new') if round_number % 2 == 0 else ('new', 'old')
            pair = {}
            for arm in order:
                start = perf_counter()
                result = (_old_complete if arm == 'old' else _new_complete)(raw, support)
                pair[arm] = dict(seconds=perf_counter() - start, **result)
            assert pair['old']['ray_sha256'] == pair['new']['ray_sha256']
            assert pair['old']['candidates'] == comb(3 * balls, 2 * balls - 1)
            assert pair['new']['candidates'] == 3 * balls
            assert pair['new']['rays'] == 2 * balls
            records.append(pair)
        cases.append(dict(balls=balls, tetrahedra=9 + 3 * balls, allowed_types=3 * balls,
            matching_nullity=2 * balls, rounds=records,
            median_original_seconds=median(record['old']['seconds'] for record in records),
            median_block_seconds=median(record['new']['seconds'] for record in records),
            median_paired_speedup=median(record['old']['seconds'] / record['new']['seconds']
                                         for record in records)))
    return dict(scope='Full supplied-sector Q-ray production, independent complete replay, and ray-list hashing. '
                      'The new arm also serializes its block certificate. No knot-recognition timing is asserted.',
                family='Embedded bipyramid ball attachments to a simplicial solid torus.', cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('audit', 'benchmark'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=3)
    parser.add_argument('--max-balls', type=int, default=5)
    arguments = parser.parse_args()
    result = audit() if arguments.action == 'audit' else benchmark(arguments.rounds, arguments.max_balls)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result.get('summary', dict(cases=len(result['cases']))), indent=2))


if __name__ == '__main__':
    main()
