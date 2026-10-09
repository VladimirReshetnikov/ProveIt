#!/usr/bin/env python3
"""Independent Regina audit of component vectors, discs, and the type bound.

Example from the research package root:
  python3 experiments/audit_normal_inventory.py --fast code \
      --output results/normal_inventory_audit.json --cases 600

Regina is an independent component/topology oracle. All tested surfaces
have explicitly bounded small normal weight; this is a correctness audit,
not a timing comparison. The RP^3 connected-sum fixture deliberately is not
a knot exterior. The generated triangulations and vectors are retained.
"""

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import random
import sys
import time
from unittest.mock import patch


SEED = 2610097311
BASE_COMMIT = '9feb4346b4d050b305f825f0f7257f495960822a'


def flat(rows):
    return tuple(value for row in rows for value in row)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def compatible(left, right):
    return all(sum(bool(a or b) for a, b in zip(x[4:], y[4:])) <= 1
               for x, y in zip(left, right))


def combination(vectors, coefficients):
    return [[sum(multiplier * vector[t][j]
                 for vector, multiplier in zip(vectors, coefficients))
             for j in range(7)] for t in range(len(vectors[0]))]


def relabel(raw, coordinates, rng):
    """Apply independent random tetrahedron/vertex names to the same surface."""
    n = len(coordinates)
    order = list(range(n))
    rng.shuffle(order)
    vertices = [rng.sample(range(4), 4) for _ in range(n)]
    faces, rows = [[None] * 4 for _ in range(n)], [[0] * 7 for _ in range(n)]
    for t, source in enumerate(raw['tetrahedra']):
        mapping = vertices[t]
        for f, pairing in enumerate(source):
            if pairing is not None:
                u = pairing['tetrahedron']
                target = [0] * 4
                for v in range(4):
                    target[mapping[v]] = vertices[u][pairing['permutation'][v]]
                faces[order[t]][mapping[f]] = {'tetrahedron': order[u],
                                                'permutation': target}
        for v in range(4):
            rows[order[t]][mapping[v]] = coordinates[t][v]
        for q in range(3):
            avoided_pair = {mapping[0], mapping[q + 1]}
            if 0 not in avoided_pair:
                avoided_pair = set(range(4)) - avoided_pair
            new_q = next(v for v in avoided_pair if v) - 1
            rows[order[t]][4 + new_q] = coordinates[t][4 + q]
    return {'tetrahedra': faces}, rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cases', type=int, default=600)
    parser.add_argument('--seed', type=int, default=SEED)
    parser.add_argument('--max-normal-disks', type=int, default=100000)
    args = parser.parse_args()
    if args.cases < 200 or args.max_normal_disks < 1:
        parser.error('--cases must be at least 200; --max-normal-disks must be positive')
    args.fast = args.fast.resolve()
    sys.path.insert(0, str(args.fast))
    import regina
    import fastunknot.normal_components as components_module
    import fastunknot.weighted_orbits as weighted_module
    from fastunknot.normal_components import (
        normal_component_inventory, verify_normal_component_certificate,
    )
    from fastunknot.integer_codec import json_safe
    from normal_orbit_research.fixtures import (
        layered_torus, boundary_cap, interior_vertex_torus,
        regina_triangulation, regina_surface, export_surface,
    )

    fixture_path = args.fast / 'normal_orbit_research/data/projective_plane_torus.json'
    source_paths = sorted((args.fast / 'fastunknot').glob('*.py'))
    source_paths += [args.fast / 'normal_orbit_research/fixtures.py', fixture_path]
    def sources():
        return {str(path.relative_to(args.fast)): digest(path.read_bytes())
                for path in source_paths}
    before = sources()
    own_hash = digest(Path(__file__).read_bytes())
    rng = random.Random(args.seed)
    all_start = time.perf_counter()

    families = []
    for size in range(1, 7):
        raw, _ = layered_torus(size)
        families.append({'name': f'layered_{size}', 'raw': raw})
    for caps in (1, 2, 3):
        raw, vector = layered_torus(2)
        for _ in range(caps):
            raw, vector = boundary_cap(raw, vector)
        families.append({'name': f'boundary_caps_{caps}', 'raw': raw})
    interior_raw, interior_basis = interior_vertex_torus()
    families.append({'name': 'interior_vertex_torus', 'raw': interior_raw})
    projective = json.loads(fixture_path.read_text())
    families.append({'name': 'projective_plane_torus', 'raw': projective['triangulation']})
    enumerations = []
    for family in families:
        native = regina_triangulation(family['raw'])
        assert native.isValid() and native.isOrientable() and not native.isIdeal()
        assert native.countBoundaryComponents() == 1
        basis = [export_surface(s) for s in regina.NormalSurfaces(native, regina.NS_STANDARD)]
        family['basis'] = basis
        enumerations.append({'family': family['name'], 'tetrahedra': native.size(),
                             'vertices': native.countVertices(),
                             'standard_vertex_surfaces': len(basis)})

    candidates, known, skipped = [], set(), []
    def add(family, name, coordinates):
        raw = family['raw']
        raw_key = digest(json.dumps(raw, sort_keys=True, separators=(',', ':')).encode())
        key = (raw_key, flat(coordinates))
        if key in known:
            return
        if sum(map(sum, coordinates)) > args.max_normal_disks:
            skipped.append({'family': family['name'], 'name': name,
                            'reason': 'declared_oracle_weight_cap',
                            'normal_disks': sum(map(sum, coordinates))})
            return
        known.add(key)
        candidates.append((family['name'], name, raw, coordinates))

    # Explicitly exercise equality in H<=v+2q: a one-sided Mobius band,
    # its two-sided frontier, and a boundary vertex-link disc coexist.
    add(families[0], 'sharp_three_types', [[1, 1, 1, 1, 0, 3, 0]])
    for family in families:
        add(family, 'empty', [[0] * 7 for _ in family['raw']['tetrahedra']])
        for index, vector in enumerate(family['basis']):
            add(family, f'vertex_surface_{index}', vector)
            add(family, f'triple_vertex_surface_{index}',
                [[3 * x for x in row] for row in vector])
    interior_family = next(f for f in families if f['name'] == 'interior_vertex_torus')
    for coefficients in product(range(5), repeat=3):
        add(interior_family, 'fixed_basis_' + '_'.join(map(str, coefficients)),
            combination([interior_basis[key] for key in
                         ('sphere', 'boundary_disk', 'mobius')], coefficients))
    projective_family = families[-1]
    for coefficients in product(range(6), repeat=2):
        add(projective_family, 'projective_and_boundary_' + '_'.join(map(str, coefficients)),
            combination([projective['coordinates'], projective['boundary_disk']],
                        coefficients))

    trials = 0
    while len(candidates) < args.cases:
        trials += 1
        if trials > args.cases * 100:
            raise RuntimeError('could not generate enough distinct compatible sums')
        family = rng.choice(families)
        basis = family['basis']
        chosen = [rng.choice(basis)]
        for _ in range(rng.randint(1, 3)):
            options = [vector for vector in basis
                       if all(compatible(vector, previous) for previous in chosen)]
            chosen.append(rng.choice(options))
        coefficients = [rng.randint(1, 7) for _ in chosen]
        add(family, f'random_compatible_{trials}', combination(chosen, coefficients))
    # Fixed vertex enumerations are retained even when they exceed --cases;
    # this argument is a target minimum, not permission to hide cases.

    rows, triangulations, coverage, max_h = [], {}, Counter(), 0
    two_sided_bound_cases = 0
    saturated = []
    def forbidden(*unused, **unused_kw):
        raise AssertionError('a search routine was called during certificate replay')

    for index, (family, name, raw, vector) in enumerate(candidates):
        changed = index % 5 == 1
        if changed:
            raw, vector = relabel(raw, vector, rng)
        raw_key = digest(json.dumps(raw, sort_keys=True, separators=(',', ':')).encode())
        triangulations[raw_key] = raw
        native = regina_triangulation(raw)
        surface = regina_surface(native, vector)
        parts = surface.components()
        oracle = Counter(flat(export_surface(part)) for part in parts)
        answer = normal_component_inventory(raw, vector, record_certificate=True)
        if answer['status'] != 'COMPLETE':
            raise AssertionError((family, name, 'unlimited extraction incomplete'))
        actual = {flat(p['coordinates']): p['multiplicity'] for p in answer['profiles']}
        if actual != dict(oracle):
            raise AssertionError((family, name, 'component-coordinate mismatch', actual, oracle))
        with patch.object(weighted_module, 'count_orbits', forbidden), \
                patch.object(components_module, '_parity_certificate', forbidden):
            if not verify_normal_component_certificate(raw, vector, answer['certificate']):
                raise AssertionError((family, name, 'certificate failed search-free replay'))

        native_profiles, topologies = {}, Counter()
        for part in parts:
            part_vector = flat(export_surface(part))
            chi = int(str(part.eulerChar()))
            orientable = bool(part.isOrientable())
            boundary = bool(part.hasRealBoundary())
            b = int(part.countBoundaries())
            compressing = bool(part.isCompressingDisc()) if chi == 1 and boundary else False
            profile = {'euler_characteristic': chi, 'orientable': orientable,
                       'two_sided': orientable, 'has_boundary': boundary,
                       'boundary_components': b, 'compressing_disk': compressing}
            if part_vector in native_profiles and native_profiles[part_vector] != profile:
                raise AssertionError('equal full vectors have different native topology')
            native_profiles[part_vector] = profile
            key = ('boundary_' if boundary else 'closed_') + \
                  ('orientable' if orientable else 'nonorientable')
            topologies[key] += 1
            if not orientable:
                doubled = [[2 * x for x in row] for row in export_surface(part)]
                frontier = regina_surface(native, doubled).components()
                if len(frontier) != 1 or not frontier[0].isOrientable():
                    raise AssertionError('one-sided normal double failed frontier property')
        expected_disks = sum(oracle[value] for value, info in native_profiles.items()
                             if info['compressing_disk'])
        if answer['compressing_disk_components'] != expected_disks:
            raise AssertionError((family, name, 'compressing-disc inventory mismatch'))
        for profile in answer['profiles']:
            value = flat(profile['coordinates'])
            info = native_profiles[value]
            if (profile['euler_characteristic'] != info['euler_characteristic']
                    or profile['disk'] != (info['euler_characteristic'] == 1
                                           and info['has_boundary'])
                    or profile['compressing_disk'] != info['compressing_disk']):
                raise AssertionError((family, name, 'component profile mismatch'))

        v = native.countVertices()
        q = sum(any(row[4:]) for row in vector)
        h = len(oracle)
        bound = v + 2 * q
        if h > bound:
            raise AssertionError((family, name, 'H>v+2q', h, v, q))
        all_two_sided = all(info['two_sided'] for info in native_profiles.values())
        if all_two_sided:
            two_sided_bound_cases += 1
            if h > v + q:
                raise AssertionError((family, name, 'two-sided H>v+q', h, v, q))
        frontiers = {value if info['two_sided'] else tuple(2 * x for x in value)
                     for value, info in native_profiles.items()}
        if len(frontiers) > v + q:
            raise AssertionError((family, name, 'too many distinct two-sided frontiers'))
        if h == bound:
            saturated.append(index)
        max_h = max(max_h, h)
        for key, count in topologies.items():
            if count:
                coverage[key] += 1
        coverage['relabelled'] += int(changed)
        coverage['contains_compressing_disk'] += int(expected_disks > 0)
        coverage['empty'] += int(not parts)
        proof = json.dumps(json_safe(answer['certificate']), sort_keys=True,
                           separators=(',', ':')).encode()
        rows.append({'id': index, 'family': family, 'case': name,
                     'triangulation_sha256': raw_key, 'coordinates': vector,
                     'relabelled': changed, 'tetrahedra': len(vector),
                     'vertices': v, 'active_quad_types': q,
                     'components': len(parts), 'distinct_vectors': h,
                     'type_bound': bound, 'all_components_two_sided': all_two_sided,
                     'distinct_two_sided_frontiers': len(frontiers),
                     'normal_disks': sum(map(sum, vector)),
                     'component_type_counts': dict(topologies),
                     'compressing_disk_components': expected_disks,
                     'profiles': answer['profiles'],
                     'native_profiles': [{'coordinates': list(value),
                                          'multiplicity': oracle[value], **info}
                                         for value, info in sorted(native_profiles.items())],
                     'certificate_verified_without_search': True,
                     'certificate_sha256': digest(proof),
                     'certificate_bytes': len(proof), 'stats': answer['stats']})
        if (index + 1) % 50 == 0:
            print(f'checked {index + 1}/{len(candidates)} cases', flush=True)

    after = sources()
    if before != after:
        raise AssertionError('source hashes changed during the audit')
    result = {'schema': 'normal-inventory-independent-audit-v1',
              'base_commit': BASE_COMMIT, 'seed': args.seed,
              'utc': datetime.now(timezone.utc).isoformat(),
              'python': platform.python_version(), 'platform': platform.platform(),
              'regina': regina.versionString(),
              'seconds': time.perf_counter() - all_start,
              'oracle_weight_cap': args.max_normal_disks,
              'comparisons': len(rows), 'two_sided_bound_comparisons': two_sided_bound_cases,
              'coverage': dict(coverage), 'maximum_distinct_vectors': max_h,
              'saturated_v_plus_2q_cases': saturated,
              'enumerations': enumerations, 'skipped': skipped,
              'triangulations': triangulations, 'cases': rows,
              'source_sha256': before, 'source_hashes_unchanged': True,
              'driver_sha256': own_hash,
              'scope': 'Native supplied finite orientable manifolds with one torus boundary; '
                       'exact Regina connected-component vectors and topology. The projective '
                       'plane fixture is not a knot exterior. No timing or search-completeness claim.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in
                      ('cases', 'triangulations', 'source_sha256')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
