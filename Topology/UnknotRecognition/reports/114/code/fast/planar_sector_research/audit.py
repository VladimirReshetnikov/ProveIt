"""Frozen-oracle audit of all selected sectors with raw nullity at most three.

The support selection is copied with attribution from
``sector_envelope_research/audit.py`` in the incoming
``unknot_minimum_envelopes_20261009`` bundle, SHA-256
42eaa2f3ead2848e06f1808719072ad7c8d3f9e479e0b49bdeb5889c3468f707.
It selects 9,995 supports on the unchanged 48-source corpus: every support
occupied by a frozen standard or quadrilateral vertex surface; the empty
support; every one- and two-tetrahedron support; 64 seeded full sectors for
sources with more than three tetrahedra; and all compatible supports on
sources with at most three tetrahedra.  Repeated supports are removed.

This is an exact finite audit, not exhaustive sector coverage on larger
triangulations and not a benchmark of the complete unknot recognizer.
Each eligible output set is compared with the complete frozen standard
vertex list restricted to that coordinate face, with pure links removed.
Only selected coverage certificates are independently replayed.
"""

import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import platform
import random

from fastunknot.sector_planar import (
    certify_planar_sector, sector_planar_plan, sector_planar_rays)
from fastunknot.sector_planar_verify import verify_planar_sector_certificate
from fastunknot.sector_sparse import PreparedSectorSource

from .fixtures import fresh_standard, ray_digest, vector_key


FAST = Path(__file__).resolve().parents[1]
REFERENCE_CORPUS_SHA256 = '0433e6c7d99bb402b79909467a7eada862ca004dc4082ee25794add0e712914e'
SOURCE_FILES = (
    'fastunknot/normal_sector.py',
    'fastunknot/normal_sector_verify.py',
    'fastunknot/normal_surface_geometry.py',
    'fastunknot/sector_sparse.py',
    'fastunknot/sector_planar.py',
    'fastunknot/sector_planar_verify.py',
    'fastunknot/integer_codec.py',
    'planar_sector_research/audit.py',
    'planar_sector_research/fixtures.py',
    'planar_sector_research/replay.py',
)


def occupied(rows):
    return tuple((i, q) for i, row in enumerate(rows)
                 for q in range(3) if row[4 + q])


def selected_supports(record):
    """Exactly preserve the prior audit's finite selection and PRNG seed."""
    count = len(record['triangulation']['tetrahedra'])
    supports = {()}
    for field in ('standard_vertices', 'quad_vertices'):
        supports.update(occupied(surface['coordinates'])
                        for surface in record[field])
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


def _wire(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode('ascii')


def _on_boundary(a, b, polygon):
    for c, d in zip(polygon, polygon[1:] + polygon[:1]):
        if all((d[0] - c[0]) * (p[1] - c[1]) ==
               (d[1] - c[1]) * (p[0] - c[0]) for p in (a, b)):
            return True
    return False


def geometry_metrics(plan):
    """Record the data entering the proved output bounds, without floats."""
    section = plan['section_dimension']
    polygon = plan['polygon']
    groups = []
    for group in plan['groups']:
        segments = set()
        if section == 2:
            for cell in group['cells']:
                vertices = cell['vertices']
                for a, b in zip(vertices, vertices[1:] + vertices[:1]):
                    if not _on_boundary(a, b, polygon):
                        segments.add(tuple(sorted((a, b))))
        groups.append(dict(vertex=group['vertex'], cells=len(group['cells']),
                           internal_edges=len(segments)))
    excess = [group['cells'] - 1 for group in groups]
    if section == -1:
        refined_bound = quadratic_bound = 0
    elif section == 0:
        refined_bound = quadratic_bound = 1
    elif section == 1:
        refined_bound = quadratic_bound = 2 + sum(excess)
    else:
        for group in groups:
            if group['internal_edges'] > 3 * (group['cells'] - 1):
                raise AssertionError(('internal edge bound', group))
        boundary_term = len(polygon) + 2 * sum(excess)
        refined_bound = boundary_term + sum(
            first['internal_edges'] * second['internal_edges']
            for first, second in combinations(groups, 2))
        quadratic_bound = boundary_term + 9 * sum(
            first * second for first, second in combinations(excess, 2))
    return dict(
        feasible_section_dimension=section,
        feasible_cone_dimension=section + 1 if section >= 0 else 0,
        polygon_vertices=len(polygon), groups=groups,
        group_records=len(groups),
        nontrivial_active_groups=sum(group['cells'] > 1 for group in groups),
        active_cells=sum(group['cells'] for group in groups),
        internal_edges=sum(group['internal_edges'] for group in groups),
        refined_ray_bound=refined_bound,
        quadratic_ray_bound=quadratic_bound,
    )


def _source_hashes():
    return {name: sha256((FAST / name).read_bytes()).hexdigest()
            for name in SOURCE_FILES}


def run(corpus_path, *, fresh_regina=False, certificate_name='planar_coverage_certificates.json'):
    data = corpus_path.read_bytes()
    corpus_sha256 = sha256(data).hexdigest()
    corpus = json.loads(data)
    hashes_before = _source_hashes()
    records, cached_sources, original_sources = [], {}, {}
    counts, dimensions, section_dimensions = Counter(), Counter(), Counter()
    strata, extrema = {}, {}
    output_digest, selection_digest = sha256(), sha256()
    unique = {name: set() for name in (
        'standard_rays', 'non_q_standard_rays', 'essential_discs',
        'non_q_essential_discs', 'd3_standard_rays', 'd3_non_q_standard_rays',
        'd3_essential_discs', 'd3_non_q_essential_discs')}
    first_extra_disc = None
    first_d3_extra_disc = None
    for source in corpus['records']:
        source_id = source['id']
        if source_id in cached_sources:
            raise ValueError('duplicate corpus source identifier')
        original_sources[source_id] = source
        prepared = PreparedSectorSource(source['triangulation'])
        cached_sources[source_id] = prepared
        originals = [(set(occupied(surface['coordinates'])), surface)
                     for surface in source['standard_vertices']]
        qkeys = {vector_key(surface['coordinates'])
                 for surface in source['quad_vertices']}
        supports = selected_supports(source)
        selection_digest.update(_wire([source_id, supports]) + b'\n')
        local_counts, local_dimensions, cases, skipped = Counter(), Counter(), [], []
        for support in supports:
            kernel = prepared.build(support)
            dimension = len(kernel.basis)
            counts['selected_supports'] += 1
            local_counts['selected_supports'] += 1
            dimensions[dimension] += 1
            local_dimensions[dimension] += 1
            if dimension > 3:
                counts['skipped_nullity_above_three'] += 1
                local_counts['skipped_nullity_above_three'] += 1
                skipped.append(dict(support=support, matching_dimension=dimension))
                continue
            stats = dict(kernel.stats)
            rays = list(sector_planar_rays(kernel, stats=stats))
            # The public plan exposes the geometry for bound and coverage
            # stratification.  Its reconstruction here is deliberate; the
            # audit measures no producer timings.
            plan = sector_planar_plan(kernel)
            metrics = geometry_metrics(plan)
            allowed = set(support)
            indices = [i for i, (positive, _) in enumerate(originals)
                       if positive and positive <= allowed]
            expected = [originals[i][1]['coordinates'] for i in indices]
            actual_set = {vector_key(rows) for rows in rays}
            expected_set = {vector_key(rows) for rows in expected}
            if actual_set != expected_set:
                raise AssertionError(dict(
                    problem='frozen standard ray mismatch', source=source_id,
                    support=support, matching_dimension=dimension,
                    missing=sorted(expected_set - actual_set),
                    unexpected=sorted(actual_set - expected_set)))
            if len(actual_set) != len(rays):
                raise AssertionError(('duplicate producer ray', source_id, support))
            if len(rays) > metrics['refined_ray_bound']:
                raise AssertionError(('ray bound violated', source_id, support, metrics))
            section = metrics['feasible_section_dimension']
            section_dimensions[(dimension, section)] += 1
            extra = [i for i in indices if vector_key(originals[i][1]['coordinates']) not in qkeys]
            discs = [i for i in indices if originals[i][1].get('essential_disc') is True]
            extra_discs = sorted(set(extra) & set(discs))
            for name, values in (('standard_rays', indices), ('non_q_standard_rays', extra),
                                 ('essential_discs', discs), ('non_q_essential_discs', extra_discs)):
                unique[name].update((source_id, i) for i in values)
                if dimension == 3:
                    unique['d3_' + name].update((source_id, i) for i in values)
            case = dict(
                support=support, matching_dimension=dimension,
                ray_count=len(rays), ray_sha256=ray_digest(rays),
                expected_standard_indices=indices,
                non_q_standard_indices=extra,
                essential_disc_indices=discs,
                non_q_essential_disc_indices=extra_discs,
                geometry=metrics, stats=stats)
            cases.append(case)
            reference = (source_id, len(cases) - 1)
            strata.setdefault((dimension, section), reference)
            for name, score in (
                ('largest_ray_list', len(rays)),
                ('most_active_groups', metrics['nontrivial_active_groups']),
                ('most_internal_edges', metrics['internal_edges']),
                ('most_cross_group_intersection_tests', stats['intersection_tests'])):
                if name not in extrema or score > extrema[name][0]:
                    extrema[name] = (score, reference)
            if extra_discs and first_extra_disc is None:
                first_extra_disc = reference
            if extra_discs and dimension == 3 and first_d3_extra_disc is None:
                first_d3_extra_disc = reference
            increments = dict(
                audited_sectors=1,
                empty_sectors=int(not rays),
                ray_occurrences=len(rays),
                non_q_ray_occurrences=len(extra),
                essential_disc_occurrences=len(discs),
                non_q_essential_disc_occurrences=len(extra_discs),
                output_bound_equalities=int(len(rays) == metrics['refined_ray_bound']))
            if dimension == 3:
                increments.update(d3_new_sectors=1, d3_ray_occurrences=len(rays),
                                  d3_non_q_ray_occurrences=len(extra),
                                  d3_essential_disc_occurrences=len(discs),
                                  d3_non_q_essential_disc_occurrences=len(extra_discs))
            counts.update(increments)
            local_counts.update(increments)
            output_digest.update(_wire([source_id, support, dimension, section,
                                        sorted(actual_set)]) + b'\n')
        records.append(dict(
            id=source_id, tetrahedra=len(source['triangulation']['tetrahedra']),
            source_sha256=prepared.source_sha256,
            counts=dict(local_counts), raw_nullity_histogram=dict(local_dimensions),
            cases=cases, skipped=skipped))
        print(source_id, dict(local_counts), flush=True)

    if corpus_sha256 == REFERENCE_CORPUS_SHA256:
        if len(records) != 48 or counts['selected_supports'] != 9995:
            raise AssertionError('the attributed reference selection changed')

    by_id = {record['id']: record for record in records}
    selected_samples = {}

    def add_sample(reference, reason):
        if reference is not None:
            selected_samples.setdefault(reference, []).append(reason)

    for (dimension, section), reference in sorted(strata.items()):
        add_sample(reference, f'raw nullity {dimension}, feasible section dimension {section}')
    for name, (_, reference) in sorted(extrema.items()):
        add_sample(reference, name)
    add_sample(first_extra_disc, 'first covered essential disc absent from the frozen Q-vertex list')
    add_sample(first_d3_extra_disc, 'first dimension-three example containing such an essential disc')

    certificates = []
    for (source_id, case_index), reasons in selected_samples.items():
        source, case = original_sources[source_id], by_id[source_id]['cases'][case_index]
        certified = certify_planar_sector(
            source['triangulation'], case['support'], source=cached_sources[source_id])
        if certified['status'] != 'COMPLETE' or ray_digest(certified['rays']) != case['ray_sha256']:
            raise AssertionError(('certificate producer disagreement', source_id, case_index))
        checker_stats = {}
        if not verify_planar_sector_certificate(source['triangulation'],
                                                  certified['certificate'], stats=checker_stats):
            raise AssertionError(('independent coverage replay failed', source_id, case_index))
        certificates.append(dict(
            source_id=source_id, case_index=case_index, reasons=reasons,
            triangulation=source['triangulation'],
            certificate=certified['certificate'],
            ray_sha256=case['ray_sha256'],
            expected_standard_indices=case['expected_standard_indices'],
            independent_replay=True, checker_stats=checker_stats))

    fresh = []
    if fresh_regina:
        preferred = (
            'cap_1_2_2', 'cap_1_2_3', 'cap_3_5_2', 'cap_3_5_3',
            'interior_1_2', 'finite_trefoil_interior',
            'finite_figureEight_interior', 'solid_torus_sum_s2xs1')
        eligible = {r['id'] for r in records if r['counts'].get('d3_new_sectors', 0)}
        choices = [name for name in preferred if name in eligible]
        candidates = sorted(records, key=lambda r: (-r['counts'].get('d3_new_sectors', 0), r['id']))
        choices.extend(r['id'] for r in candidates
                       if r['id'] in eligible and r['id'] not in choices)
        for source_id in choices[:8]:
            source = original_sources[source_id]
            regenerated = fresh_standard(source['triangulation'])
            expected = [s['coordinates'] for s in source['standard_vertices']]
            if {vector_key(s) for s in regenerated} != {vector_key(s) for s in expected}:
                raise AssertionError(('fresh Regina complete-list mismatch', source_id))
            fresh.append(dict(
                source_id=source_id, standard_vertices=len(regenerated),
                ray_sha256=ray_digest(regenerated), full_list_matches_frozen=True,
                d3_selected_sectors=by_id[source_id]['counts']['d3_new_sectors']))
            print('fresh Regina full standard list:', source_id, len(regenerated), flush=True)

    hashes_after = _source_hashes()
    if hashes_after != hashes_before:
        raise RuntimeError('audited source files changed during this run; rerun on a stable snapshot')
    answer = dict(
        schema='planar-sector-corpus-audit-v1',
        scope='finite selected sectors; exact complete non-link standard rays per audited sector',
        python=platform.python_version(),
        corpus_sha256=corpus_sha256, corpus_schema=corpus.get('schema'),
        frozen_regina_version=corpus.get('regina_version'),
        input_triangulations=len(records), prepared_sources_built=len(cached_sources),
        reference_selection_attribution=__doc__,
        reference_selection_source_sha256='42eaa2f3ead2848e06f1808719072ad7c8d3f9e479e0b49bdeb5889c3468f707',
        source_sha256=hashes_before,
        selection_sha256=selection_digest.hexdigest(),
        complete_output_sha256=output_digest.hexdigest(),
        counts=dict(counts), raw_nullity_histogram=dict(sorted(dimensions.items())),
        raw_and_feasible_section_histogram=[dict(matching_dimension=d,
            feasible_section_dimension=e, sectors=count)
            for (d, e), count in sorted(section_dimensions.items())],
        unique_covered={name: dict(count=len(values),
            source_and_standard_index=sorted(values)) for name, values in unique.items()},
        extrema={name: dict(value=score, source_id=ref[0], case_index=ref[1])
                 for name, (score, ref) in sorted(extrema.items())},
        records=records,
        coverage_certificates=dict(file=certificate_name, count=len(certificates),
            all_independently_replayed=True,
            strata=[dict(matching_dimension=d, feasible_section_dimension=e)
                    for d, e in sorted(strata)]),
        fresh_regina=fresh)
    if fresh_regina:
        import regina
        answer['fresh_regina_version'] = regina.versionString()
    certificate_bundle = dict(schema='planar-sector-coverage-samples-v1',
        corpus_sha256=corpus_sha256, complete_output_sha256=output_digest.hexdigest(),
        records=certificates)
    return answer, certificate_bundle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--certificates', type=Path)
    parser.add_argument('--fresh-regina', action='store_true')
    args = parser.parse_args()
    certificates_path = args.certificates or args.output.with_name('planar_coverage_certificates.json')
    answer, certificates = run(args.corpus, fresh_regina=args.fresh_regina,
                               certificate_name=certificates_path.name)
    for path, value in ((args.output, answer), (certificates_path, certificates)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    print('COMPLETE', answer['counts'], flush=True)
    print('output set SHA-256', answer['complete_output_sha256'], flush=True)


if __name__ == '__main__':
    main()
