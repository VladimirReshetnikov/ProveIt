"""Broad, source-frozen sector Euler audit against complete Regina ray lists.

The two timing columns are exploratory one-shot observations.  They are not
paired recognition benchmarks.  Every complete new answer is independently
replayed, and every complete screen is compared to both frozen Q and standard
vertex lists after canonical vertex-link removal.
"""

import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from math import gcd
from pathlib import Path
import random
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'work' / 'fast' if (ROOT / 'work').exists() else ROOT / 'fast'))
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_sector import build_sector_kernel, sector_rays, SearchLimit
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_ray import certify_normal_ray_disc
from fastunknot.normal_ray_verify import verify_normal_ray_disc


def canonical(prepared, original):
    rows = [list(row) for row in original]
    minima = {}
    for t, row in enumerate(rows):
        for v in range(4):
            root = prepared['vertex_roots'][4*t+v]
            minima[root] = min(minima.get(root, row[v]), row[v])
    for t, row in enumerate(rows):
        for v in range(4):
            row[v] -= minima[prepared['vertex_roots'][4*t+v]]
    return rows


def q_key(rows):
    flat = [x for row in rows for x in row[4:]]
    common = 0
    for x in flat:
        common = gcd(common, x)
    return tuple(x//common for x in flat) if common else tuple(flat)


def oracle_vertices(prepared, vertices):
    result = []
    for index, vertex in enumerate(vertices):
        rows = canonical(prepared, vertex['coordinates'])
        occupied = frozenset((t, q) for t, row in enumerate(rows)
                             for q in range(3) if row[4+q])
        if not occupied:
            continue
        chi = _coordinates(prepared, rows, lambda: None)['euler_characteristic']
        result.append(dict(index=index, occupied=occupied, chi=chi, key=q_key(rows),
                           essential_disc=vertex['essential_disc']))
    return result


def selections(fixture, rng, random_sectors):
    n = fixture['tetrahedra']
    choices = {}
    def add(values, origin):
        choices.setdefault(tuple(values), set()).add(origin)
    if n <= 5:
        for types in product(range(3), repeat=n):
            add(types, 'all_full_sectors_t_le_5')
    else:
        for _ in range(random_sectors):
            add([rng.randrange(3) for _ in range(n)], 'random_full_sector')
    for kind in ('quad_vertices', 'standard_vertices'):
        for vertex in fixture[kind]:
            add(vertex['full_sector_quad_types'], kind+'_full_extension')
            exact = [-1]*n
            for t, row in enumerate(vertex['coordinates']):
                for q in range(3):
                    if row[4+q]:
                        exact[t] = q
            add(exact, kind+'_occupied_support')
    return [(values, sorted(origins)) for values, origins in sorted(choices.items())]


def old_screen(raw, support, max_bases):
    kernel = build_sector_kernel(raw, support)
    stats = dict(kernel.stats)
    try:
        for rows in sector_rays(kernel, phase='quadrilateral', max_bases=max_bases, stats=stats):
            if _coordinates(kernel.prepared, rows, lambda: None)['euler_characteristic'] > 0:
                return dict(status='POSITIVE_EULER', stats=stats)
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    return dict(status='NO_POSITIVE_EULER', stats=stats)


def run(args):
    encoded = args.input.read_bytes()
    corpus = json.loads(encoded)
    rng = random.Random(args.seed)
    records, failures, fixture_summaries = [], [], []
    totals = Counter()
    started = perf_counter()
    for fixture in corpus['records']:
        raw = fixture['triangulation']
        prepared = _prepare(raw, lambda: None)
        q_oracle = oracle_vertices(prepared, fixture['quad_vertices'])
        standard_oracle = oracle_vertices(prepared, fixture['standard_vertices'])
        q_lookup = {vertex['key']: vertex for vertex in q_oracle}
        before = len(records)
        for choices, origins in selections(fixture, rng, args.random_sectors):
            support = [(t, q) for t, q in enumerate(choices) if q >= 0]
            selected = frozenset(support)
            expected_q = any(vertex['chi'] > 0 and vertex['occupied'] <= selected for vertex in q_oracle)
            expected_standard = any(vertex['chi'] > 0 and vertex['occupied'] <= selected
                                    for vertex in standard_oracle)
            start = perf_counter()
            old = old_screen(raw, support, args.max_bases)
            old_seconds = perf_counter()-start
            start = perf_counter()
            new = decide_sector_euler(raw, support, max_anchors=args.max_anchors,
                                      max_pivots=args.max_pivots)
            new_seconds = perf_counter()-start
            start = perf_counter()
            envelope = decide_sector_euler(raw, support, strategy='envelope',
                                           max_anchors=args.max_anchors,
                                           max_pivots=args.max_pivots)
            envelope_seconds = perf_counter()-start
            replay_seconds = 0
            verified = None
            if new['status'] != 'INCONCLUSIVE':
                start = perf_counter()
                verified = verify_sector_euler_certificate(raw, new['certificate'])
                replay_seconds = perf_counter()-start
            envelope_verified = None
            envelope_replay_seconds = 0
            if envelope['status'] != 'INCONCLUSIVE':
                start = perf_counter()
                envelope_verified = verify_sector_euler_certificate(raw, envelope['certificate'])
                envelope_replay_seconds = perf_counter()-start
            error = []
            if expected_q != expected_standard:
                error.append('Q and standard oracle positivity disagree')
            for name, answer in (('old', old), ('new', new), ('envelope', envelope)):
                if answer['status'] != 'INCONCLUSIVE' and (
                        answer['status'] == 'POSITIVE_EULER') != expected_q:
                    error.append(name+' disagrees with frozen oracle')
            if verified is False:
                error.append('independent Euler replay rejected')
            if envelope_verified is False:
                error.append('independent envelope-strategy replay rejected')
            ray_check = None
            if new['status'] == 'POSITIVE_EULER':
                key = q_key(new['coordinates'])
                reference = q_lookup.get(key)
                if reference is None:
                    error.append('returned basic ray is absent from complete Q oracle')
                ray = certify_normal_ray_disc(raw, new['coordinates'])
                ray_check = dict(status=ray['status'],
                                 expected=None if reference is None else reference['essential_disc'])
                if ray['status'] == 'DISC_FOUND':
                    ray_check['verified'] = verify_normal_ray_disc(raw, new['coordinates'], ray['certificate'])
                    if not ray_check['verified']:
                        error.append('independent primitive-ray disc replay rejected')
                    if reference is not None and not reference['essential_disc']:
                        error.append('primitive-ray disc disagrees with frozen Q oracle')
                totals['positive_rays'] += 1
                totals['primitive_disc_proofs'] += ray['status'] == 'DISC_FOUND'
            envelope_ray_check = None
            if envelope['status'] == 'POSITIVE_EULER':
                key = q_key(envelope['coordinates'])
                reference = q_lookup.get(key)
                if reference is None:
                    error.append('envelope fallback ray is absent from complete Q oracle')
                ray = certify_normal_ray_disc(raw, envelope['coordinates'])
                envelope_ray_check = dict(status=ray['status'],
                    expected=None if reference is None else reference['essential_disc'])
                if ray['status'] == 'DISC_FOUND':
                    envelope_ray_check['verified'] = verify_normal_ray_disc(
                        raw, envelope['coordinates'], ray['certificate'])
                    if not envelope_ray_check['verified']:
                        error.append('envelope fallback primitive-disc replay rejected')
                    if reference is not None and not reference['essential_disc']:
                        error.append('envelope fallback disc disagrees with frozen Q oracle')
                totals['envelope_positive_rays'] += 1
                totals['envelope_primitive_disc_proofs'] += ray['status'] == 'DISC_FOUND'
            envelope_record = dict(status=envelope['status'], stats=envelope['stats'],
                verified=envelope_verified, ray_check=envelope_ray_check,
                exploratory_seconds=dict(producer=envelope_seconds,
                                         independent_replay=envelope_replay_seconds))
            if envelope['status'] != 'INCONCLUSIVE':
                envelope_record['certificate'] = envelope['certificate']
            record = dict(fixture_id=fixture['id'], support=[list(pair) for pair in support],
                origins=origins, tetrahedra=fixture['tetrahedra'], vertices=fixture['vertices'],
                expected_q_positive=expected_q, expected_standard_positive=expected_standard,
                old_status=old['status'], old_stats=old['stats'],
                new_status=new['status'], new_stats=new['stats'], verified=verified,
                exploratory_seconds=dict(old_screen=old_seconds, new_producer=new_seconds,
                                         new_independent_replay=replay_seconds),
                ray_check=ray_check, envelope=envelope_record)
            if new['status'] != 'INCONCLUSIVE':
                record['certificate'] = new['certificate']
            if error:
                record['errors'] = error
                failures.append(dict(fixture_id=fixture['id'], support=record['support'], errors=error))
            records.append(record)
            totals['sectors'] += 1
            totals['old_'+old['status']] += 1
            totals['new_'+new['status']] += 1
            totals['envelope_'+envelope['status']] += 1
            totals['envelope_compact_proofs'] += envelope.get('certificate', {}).get('proof_kind') == 'envelope'
            totals['independent_replays'] += verified is True
            totals['envelope_independent_replays'] += envelope_verified is True
            totals['new_reused_anchors'] += new['stats']['reused_anchors']
            totals['envelope_reused_anchors'] += envelope['stats']['reused_anchors']
        local = records[before:]
        summary = dict(fixture_id=fixture['id'], sectors=len(local),
                       maximum_matching_nullity=max(r['new_stats']['matching_nullity'] for r in local),
                       maximum_active_vertices=max(r['new_stats']['active_vertices'] for r in local),
                       maximum_anchors=max(r['new_stats']['anchors_total'] for r in local))
        fixture_summaries.append(summary)
        print(json.dumps(summary), flush=True)
    result = dict(schema='normal-sector-euler-audit-v1', seed=args.seed,
        input_sha256=sha256(encoded).hexdigest(), oracle_regina_version=corpus['regina_version'],
        fixture_count=len(corpus['records']), selection='all full sectors for t<=5; '
            'seeded random full sectors above five; every frozen standard/Q vertex full extension '
            'and occupied support, deduplicated', random_sectors=args.random_sectors,
        allowances=dict(max_bases=args.max_bases, max_pivots=args.max_pivots,
                        max_anchors=args.max_anchors),
        source_sha256={name: sha256(path.read_bytes()).hexdigest() for name, path in (
            ('fast/fastunknot/exact_lp.py', Path(sys.modules['fastunknot.exact_lp'].__file__)),
            ('fast/fastunknot/normal_euler.py', Path(sys.modules['fastunknot.normal_euler'].__file__)),
            ('fast/fastunknot/normal_euler_verify.py', Path(sys.modules['fastunknot.normal_euler_verify'].__file__)),
            ('scripts/audit_sector_euler.py', Path(__file__)))},
        timing_scope='single-shot exploratory supplied-sector screens; not paired recognition timings',
        summary=dict(totals), wall_seconds=perf_counter()-started,
        failures=failures, fixture_summaries=fixture_summaries, records=records)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(result['summary'], failures=len(failures), wall_seconds=result['wall_seconds'])), flush=True)
    if failures:
        raise SystemExit('sector Euler audit failed; see recorded counterexamples')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, default=ROOT/'results/discovery_corpus.json')
    parser.add_argument('--output', type=Path, default=ROOT/'results/sector_euler_audit.json')
    parser.add_argument('--seed', type=int, default=261009527)
    parser.add_argument('--random-sectors', type=int, default=64)
    parser.add_argument('--max-bases', type=int, default=50000)
    parser.add_argument('--max-pivots', type=int, default=20000)
    parser.add_argument('--max-anchors', type=int, default=10000)
    run(parser.parse_args())
