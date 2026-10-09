#!/usr/bin/env python3
"""Independent, bounded Regina oracle for the normal-topology spectrum.

Run from any directory, with Regina 7.4 (or another recorded version) installed::

    python topology_research/regina_audit.py generate --corpus CORPUS.json
    python topology_research/regina_audit.py audit --corpus CORPUS.json \
        --output RESULTS.json --recheck-oracle

The ``run`` command performs both steps.  Ordinary ``audit`` replays the frozen
oracle answers and does not require Regina.  Generation and oracle rechecking
use Regina's own matching equations, explicit connected components, Euler
characteristics, boundary counts and orientability tests.  Neither uses the
producer's geometry, orbit code, coordinate core, or topology reconstruction.
The two JSON fixtures and the pure ``interior_vertex_torus`` input constructor
are reused only to specify input face pairings and vectors.

These are finite regression experiments, not complexity or correctness proofs.
Regina's component/boundary/orientation routines may expand normal discs, so
the corpus strictly bounds the total number of normal discs.  Large binary
coordinate experiments belong in a different benchmark.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
import sys
import time
import traceback


FAST_ROOT = Path(__file__).resolve().parents[1]
if str(FAST_ROOT) not in sys.path:
    sys.path.insert(0, str(FAST_ROOT))

SCHEMA = 'regina-topology-audit-corpus-v1'
SEED = 20261009
MAX_DISCS = 5000


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def flat(rows):
    return [value for row in rows for value in row]


def rows_of(vector):
    return [list(vector[i:i + 7]) for i in range(0, len(vector), 7)]


def export_triangulation(triangulation):
    return {'tetrahedra': [[
        None if tetrahedron.adjacentTetrahedron(face) is None else {
            'tetrahedron': tetrahedron.adjacentTetrahedron(face).index(),
            'permutation': [tetrahedron.adjacentGluing(face)[v]
                            for v in range(4)]}
        for face in range(4)] for tetrahedron in triangulation.tetrahedra()]}


def import_triangulation(raw, regina):
    result = regina.Triangulation3()
    for _ in raw['tetrahedra']:
        result.newTetrahedron()
    for t, row in enumerate(raw['tetrahedra']):
        for f, record in enumerate(row):
            if record is not None and result.tetrahedron(t).adjacentTetrahedron(f) is None:
                result.tetrahedron(t).join(
                    f, result.tetrahedron(record['tetrahedron']),
                    regina.Perm4(*record['permutation']))
    # The round trip also checks that the supplied reciprocal gluings agree.
    if export_triangulation(result) != raw:
        raise ValueError('Regina face-pairing round trip changed the input')
    return result


def export_vector(surface):
    return [value for t in range(surface.triangulation().size()) for value in
            [*[int(str(surface.triangles(t, v))) for v in range(4)],
             *[int(str(surface.quads(t, q))) for q in range(3)]]]


def histogram_rows(counter):
    return [dict(chi=chi, boundary_components=b, orientable=orientable,
                 multiplicity=multiplicity)
            for (chi, b, orientable), multiplicity in sorted(counter.items())
            if multiplicity]


def histogram_counter(rows):
    result = Counter()
    for row in rows:
        result[row['chi'], row['boundary_components'], row['orientable']] += row['multiplicity']
    return result


def quad_compatible(vectors):
    if not vectors:
        return True
    return all(sum(any(vector[i + q] for vector in vectors) for q in range(3)) <= 1
               for i in range(4, len(vectors[0]), 7))


class ReginaOracle:
    """Regina alone supplies the ambient and surface validity checks."""

    def __init__(self, triangulation, regina):
        self.triangulation = triangulation
        self.regina = regina
        t = triangulation
        if not (t.isValid() and t.isConnected() and t.isOrientable()
                and not t.isIdeal() and t.countBoundaryComponents() == 1
                and t.boundaryComponent(0).eulerChar() == 0):
            raise ValueError('oracle corpus requires a compact orientable one-torus manifold')
        matrix = regina.makeMatchingEquations(t, regina.NormalCoords.Standard)
        self.equations = [
            [(j, int(str(matrix.entry(i, j)))) for j in range(matrix.columns())
             if matrix.entry(i, j) != 0]
            for i in range(matrix.rows())]
        self.cache = {}

    def census(self, vector):
        vector = tuple(vector)
        if vector in self.cache:
            return self.cache[vector]
        if len(vector) != 7 * self.triangulation.size():
            raise ValueError('wrong coordinate dimension')
        if any(type(value) is not int or value < 0 for value in vector):
            raise ValueError('nonnegative integer coordinates required')
        if sum(vector) > MAX_DISCS:
            raise ValueError('Regina explicit-disc bound exceeded')
        if any(sum(vector[j] * coefficient for j, coefficient in equation)
               for equation in self.equations):
            raise ValueError('Regina matching equations are not satisfied')
        if not quad_compatible([vector]):
            raise ValueError('quadrilateral constraints are not satisfied')
        surface = self.regina.NormalSurface(
            self.triangulation, self.regina.NormalCoords.Standard, list(vector))
        if not surface.embedded() or not surface.isCompact():
            raise ValueError('Regina did not accept a compact embedded surface')
        pieces = surface.components()
        counter = Counter()
        summed_vector = [0] * len(vector)
        for component in pieces:
            if not component.isConnected():
                raise ArithmeticError('Regina components() returned a disconnected piece')
            chi = int(str(component.eulerChar()))
            boundaries = component.countBoundaries()
            orientable = component.isOrientable()
            if orientable:
                if (2 - boundaries - chi) < 0 or (2 - boundaries - chi) % 2:
                    raise ArithmeticError('Regina output violates orientable classification')
            elif 2 - boundaries - chi < 1:
                raise ArithmeticError('Regina output violates nonorientable classification')
            counter[chi, boundaries, orientable] += 1
            for i, value in enumerate(export_vector(component)):
                summed_vector[i] += value
        if tuple(summed_vector) != vector:
            raise ArithmeticError('Regina component vectors do not add to the input')
        if sum(chi * count for (chi, _, _), count in counter.items()) != int(str(surface.eulerChar())):
            raise ArithmeticError('Regina Euler characteristic disagrees with its components')
        if sum(b * count for (_, b, _), count in counter.items()) != surface.countBoundaries():
            raise ArithmeticError('Regina boundary count disagrees with its components')
        answer = histogram_rows(counter)
        self.cache[vector] = answer
        return answer


def cap_boundary_face(triangulation, regina):
    """Glue a new ball tetrahedron along one boundary triangle, then enumerate."""
    result = regina.Triangulation3(triangulation)
    t, f = next((tet.index(), f) for tet in result.tetrahedra()
                for f in range(4) if tet.adjacentTetrahedron(f) is None)
    new = result.newTetrahedron()
    permutation = [0] * 4
    permutation[f] = 3
    for image, v in enumerate(v for v in range(4) if v != f):
        permutation[v] = image
    result.tetrahedron(t).join(f, new, regina.Perm4(*permutation))
    return result


def compactify(triangulation, regina):
    if triangulation.isIdeal():
        triangulation.idealToFinite()
        triangulation.simplify()
    return regina.Triangulation3.fromIsoSig(triangulation.isoSig())


def relabel(raw, vector, order, vertex_maps):
    """Transform all faces and standard coordinates under a simplicial relabeling.

    Quadrilateral q avoids edges {0,q+1} and its complementary pair.  Regina's
    own matching matrix subsequently validates the transformed coordinates.
    """
    size = len(raw['tetrahedra'])
    faces = [[None] * 4 for _ in range(size)]
    rows = [[0] * 7 for _ in range(size)]
    source = rows_of(vector)
    for t, row in enumerate(raw['tetrahedra']):
        mapping = vertex_maps[t]
        for f, record in enumerate(row):
            if record is None:
                continue
            u, p = record['tetrahedron'], record['permutation']
            transformed = [0] * 4
            for v in range(4):
                transformed[mapping[v]] = vertex_maps[u][p[v]]
            faces[order[t]][mapping[f]] = dict(tetrahedron=order[u],
                                              permutation=transformed)
        for v in range(4):
            rows[order[t]][mapping[v]] = source[t][v]
        for q in range(3):
            pair = {mapping[0], mapping[q + 1]}
            if 0 not in pair:
                pair = set(range(4)) - pair
            target = next(v for v in pair if v != 0) - 1
            rows[order[t]][4 + target] = source[t][4 + q]
    return {'tetrahedra': faces}, flat(rows)


def generate_corpus(path):
    import regina
    from normal_orbit_research.fixtures import interior_vertex_torus

    started = time.monotonic()
    rng = random.Random(SEED)
    regina.RandomEngine.reseedWithDefault()
    corpus = dict(schema=SCHEMA, created_utc=timestamp(), seed=SEED,
        regina_version=regina.versionString(), python_version=platform.python_version(),
        platform=platform.platform(), regina_random_seed='RandomEngine.reseedWithDefault()',
        generator_sha256=file_hash(__file__), max_normal_discs=MAX_DISCS,
        oracle_methods=['makeMatchingEquations(Standard)', 'NormalSurface.components()',
                        'NormalSurface.eulerChar()', 'NormalSurface.countBoundaries()',
                        'NormalSurface.isOrientable()'],
        limitations=['Bounded explicit-disc experiments do not establish asymptotic complexity.',
                     'Regeneration fixes both Python and Regina seeds; Regina random decisions may differ with the release, operating system, architecture or compiler. Frozen face pairings and vectors are the portable reproduction source.',
                     'Relabelings increase labeled inputs, not triangulation isomorphism classes.'],
        fixture_hashes={}, triangulations={}, cases=[], enumeration=[])
    corpus['fixture_hashes']['normal_orbit_research/fixtures.py'] = file_hash(
        FAST_ROOT / 'normal_orbit_research/fixtures.py')
    seeds = []
    for a, b in [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
                 (2, 3), (2, 5), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 7)]:
        t = regina.Example3.lst(a, b)
        seeds.append((f'lst-{a}-{b}', compactify(t, regina), [],
                      f'Regina Example3.lst({a},{b})'))
    capped = regina.Example3.lst(2, 3)
    for caps in (1, 2):
        capped = cap_boundary_face(capped, regina)
        seeds.append((f'boundary-caps-{caps}', compactify(capped, regina), [],
                      f'LST(2,3), then {caps} tetrahedron attachments along boundary faces'))
    raw, basis = interior_vertex_torus()
    seeds.append(('interior-vertex', import_triangulation(raw, regina),
                  [(name, flat(rows)) for name, rows in basis.items()],
                  'Fixed 1-4 subdivision from normal_orbit_research.fixtures'))
    for name, relative in [
            ('projective-plane', 'normal_orbit_research/data/projective_plane_torus.json'),
            ('klein-bottle', 'topology_research/data/klein_torus.json')]:
        fixture_path = FAST_ROOT / relative
        fixture = json.loads(fixture_path.read_text())
        corpus['fixture_hashes'][relative] = file_hash(fixture_path)
        supplied = [('distinguished', flat(fixture['coordinates']))]
        if 'boundary_disk' in fixture:
            supplied.append(('boundary-disk', flat(fixture['boundary_disk'])))
        seeds.append((name, import_triangulation(fixture['triangulation'], regina),
                      supplied, f'Frozen input fixture {relative}'))
    for name, t in [('trefoil', regina.Example3.trefoil()),
                    ('figure-eight', regina.Example3.figureEight())]:
        seeds.append((name, compactify(t, regina), [],
                      f'Regina Example3.{"figureEight" if name == "figure-eight" else "trefoil"}(); idealToFinite(); simplify()'))
    for p, q in [(2, 5), (2, 7), (3, 4), (3, 5)]:
        t = regina.ExampleLink.torus(p, q).complement()
        seeds.append((f'torus-knot-{p}-{q}', compactify(t, regina), [],
                      f'Regina ExampleLink.torus({p},{q}).complement(); idealToFinite(); simplify()'))

    seen_cases = set()

    def register_triangulation(name, t, source, extra=None):
        raw = export_triangulation(t)
        corpus['triangulations'][name] = dict(
            triangulation=raw, sha256=digest(raw), iso_sig=t.isoSig(),
            tetrahedra=t.size(), vertices=t.countVertices(),
            boundary_components=t.countBoundaryComponents(),
            boundary_euler_characteristic=int(str(t.boundaryComponent(0).eulerChar())),
            valid=t.isValid(), connected=t.isConnected(), orientable=t.isOrientable(),
            ideal=t.isIdeal(), source=source, **(extra or {}))
        return raw

    def add_case(name, vector, provenance, oracle):
        vector = list(vector)
        if sum(vector) > MAX_DISCS:
            return False
        key = name, tuple(vector)
        if key in seen_cases:
            return False
        expected = oracle.census(vector)
        record = dict(id=f'case-{len(corpus["cases"]):04d}', triangulation_id=name,
                      coordinates=rows_of(vector), provenance=provenance,
                      normal_discs=sum(vector), maximum_coordinate=max(vector, default=0),
                      oracle=expected, oracle_sha256=digest(expected))
        record['input_sha256'] = digest(dict(
            triangulation=corpus['triangulations'][name]['triangulation'],
            coordinates=record['coordinates']))
        corpus['cases'].append(record)
        seen_cases.add(key)
        return True

    for name, t, supplied, source in seeds:
        register_triangulation(name, t, source)
        oracle = ReginaOracle(t, regina)
        before = len(corpus['cases'])
        add_case(name, [0] * (7 * t.size()), {'kind': 'empty'}, oracle)
        tick = time.monotonic()
        surfaces = regina.NormalSurfaces(t, regina.NormalCoords.Standard,
            regina.NormalList.Vertex | regina.NormalList.EmbeddedOnly)
        vectors = [(i, export_vector(surface)) for i, surface in enumerate(surfaces)]
        bounded = [(i, vector) for i, vector in vectors if sum(vector) <= MAX_DISCS]
        corpus['enumeration'].append(dict(triangulation_id=name, count=surfaces.size(),
            bounded_count=len(bounded), seconds=time.monotonic() - tick,
            selection='8 preferred distinct topology patterns/extreme Euler values, then scales and compatible sums'))
        # Explore distinct topology patterns before repeated vertex-link patterns.
        ranked = sorted(bounded, key=lambda item: (
            min((row['chi'] for row in oracle.census(item[1])), default=0),
            -max((row['boundary_components'] for row in oracle.census(item[1])), default=0),
            sum(item[1]), item[0]))
        candidates, used_vectors, used_histograms = [], set(), set()
        for label, vector in supplied:
            candidates.append((dict(kind='fixture', label=label), vector))
            used_vectors.add(tuple(vector))
            used_histograms.add(digest(oracle.census(vector)))
        for unique_pattern in (True, False):
            for index, vector in ranked:
                if len(candidates) >= 8:
                    break
                signature = digest(oracle.census(vector))
                if tuple(vector) in used_vectors or (unique_pattern and signature in used_histograms):
                    continue
                candidates.append((dict(kind='Regina vertex', index=index), vector))
                used_vectors.add(tuple(vector))
                used_histograms.add(signature)
        for provenance, vector in candidates:
            add_case(name, vector, provenance, oracle)
        for provenance, vector in candidates[:2]:
            for coefficient in (2, 3, 4, 5):
                add_case(name, [coefficient * value for value in vector],
                         dict(kind='scale', coefficient=coefficient, base=provenance), oracle)
        # All sums satisfy the quadrilateral condition, and Regina's independent
        # matching equations are checked for each resulting vector before use.
        attempts = 0
        target = 36 if name in ('figure-eight', 'projective-plane') else 22
        while len(corpus['cases']) - before < target and attempts < 3000:
            attempts += 1
            pool = supplied + [(f'vertex-{index}', vector) for index, vector in bounded]
            rng.shuffle(pool)
            chosen = []
            for label, vector in pool:
                if quad_compatible([item[1] for item in chosen] + [vector]):
                    chosen.append((label, vector))
                if len(chosen) >= rng.randint(2, 4):
                    break
            coefficients = [rng.randint(1, 7) for _ in chosen]
            vector = [sum(coefficient * term[j] for coefficient, (_, term)
                          in zip(coefficients, chosen)) for j in range(7 * t.size())]
            add_case(name, vector, dict(kind='random compatible sum',
                terms=[dict(basis=label, coefficient=coefficient)
                       for coefficient, (label, _) in zip(coefficients, chosen)]), oracle)
        if len(corpus['cases']) - before < target:
            raise RuntimeError(f'could not generate {target} distinct bounded cases for {name}')
        print(f'generated {name}: {len(corpus["cases"]) - before} cases, '
              f'{surfaces.size()} vertex normals, {t.size()} tetrahedra', flush=True)

    # Labels are deliberately noncanonical; Regina recomputes the oracle after
    # checking the transformed matching equations, rather than copying answers.
    for original in ['lst-1-2', 'lst-3-5', 'boundary-caps-2', 'interior-vertex',
                     'projective-plane', 'klein-bottle', 'trefoil', 'figure-eight']:
        entry = corpus['triangulations'][original]
        t_count = entry['tetrahedra']
        order = rng.sample(range(t_count), t_count)
        maps = [rng.sample(range(4), 4) for _ in range(t_count)]
        original_cases = [case for case in corpus['cases'] if case['triangulation_id'] == original]
        selected = [original_cases[i] for i in sorted(set(
            [0, 1, 2, len(original_cases) - 1] + rng.sample(range(len(original_cases)), 4)))]
        while len(selected) < 8:
            candidate = rng.choice(original_cases)
            if candidate not in selected:
                selected.append(candidate)
        name = original + '-relabeled'
        raw, _ = relabel(entry['triangulation'], flat(selected[0]['coordinates']), order, maps)
        t = import_triangulation(raw, regina)
        if t.isoSig() != entry['iso_sig']:
            raise ArithmeticError('relabeling changed the triangulation isomorphism signature')
        register_triangulation(name, t, f'Simplicial relabeling of {original}',
                               dict(tetrahedron_order=order, vertex_maps=maps))
        oracle = ReginaOracle(t, regina)
        for original_case in selected:
            _, vector = relabel(entry['triangulation'], flat(original_case['coordinates']), order, maps)
            if oracle.census(vector) != original_case['oracle']:
                raise ArithmeticError('Regina detected a relabeling topology mismatch')
            add_case(name, vector, dict(kind='simplicial relabeling',
                                       original_case=original_case['id']), oracle)
    corpus['generation_seconds'] = time.monotonic() - started
    corpus['corpus_sha256'] = digest(corpus)
    write_json(path, corpus)
    print(f'frozen {len(corpus["cases"])} cases on {len(corpus["triangulations"])} labeled '
          f'triangulations, {len({t["iso_sig"] for t in corpus["triangulations"].values()})} '
          f'isomorphism classes; sha256={corpus["corpus_sha256"]}', flush=True)
    return corpus


def verify_corpus_hashes(corpus):
    if corpus.get('schema') != SCHEMA:
        raise ValueError('unknown corpus schema')
    copy = dict(corpus)
    recorded = copy.pop('corpus_sha256')
    if digest(copy) != recorded:
        raise ValueError('corpus content hash mismatch')
    for entry in corpus['triangulations'].values():
        if digest(entry['triangulation']) != entry['sha256']:
            raise ValueError('triangulation hash mismatch')
    for case in corpus['cases']:
        raw = corpus['triangulations'][case['triangulation_id']]['triangulation']
        if digest(dict(triangulation=raw, coordinates=case['coordinates'])) != case['input_sha256']:
            raise ValueError('case input hash mismatch')
        if digest(case['oracle']) != case['oracle_sha256']:
            raise ValueError('case oracle hash mismatch')
        if sum(flat(case['coordinates'])) != case['normal_discs'] or case['normal_discs'] > MAX_DISCS:
            raise ValueError('frozen coordinate bound mismatch')


def runtime_hashes():
    return {str(path.relative_to(FAST_ROOT)): file_hash(path)
            for path in sorted((FAST_ROOT / 'fastunknot').rglob('*.py'))}


def run_audit(corpus, output, *, recheck_oracle=False, timeout=30.0, limit=None):
    from fastunknot.normal_topology import normal_topology_spectrum
    from fastunknot.normal_topology_verify import verify_normal_topology_spectrum

    verify_corpus_hashes(corpus)
    source_before = runtime_hashes()
    started = time.monotonic()
    report = dict(schema='regina-topology-audit-results-v1', created_utc=timestamp(),
        complete=False, corpus_sha256=corpus['corpus_sha256'],
        audit_script_sha256=file_hash(__file__), runtime_sources=source_before,
        runtime_sources_sha256=digest(source_before),
        platform=platform.platform(), python_version=platform.python_version(),
        regina_version=corpus['regina_version'], fresh_oracle_recheck=recheck_oracle,
        oracle_description='Regina explicit components, Euler characteristic, boundary count and orientability; independent matching-equation and normal-vector checks',
        certificate_storage='Every produced certificate is independently verified; canonical hashes and byte lengths are retained, and certificates can be regenerated from frozen inputs.',
        mode_description='direct and quadrilateral-core for every case; classical AHT periodic rule on every tenth case as an additional control',
        timeout_seconds_per_producer_or_verifier=timeout, cases=[], failures=[])
    oracles = {}
    if recheck_oracle:
        import regina
        report['recheck_regina_version'] = regina.versionString()
        for name, entry in corpus['triangulations'].items():
            oracles[name] = ReginaOracle(import_triangulation(entry['triangulation'], regina), regina)
    cases = corpus['cases'] if limit is None else corpus['cases'][:limit]
    calls = 0
    type_occurrences = Counter()
    for index, case in enumerate(cases):
        raw = corpus['triangulations'][case['triangulation_id']]['triangulation']
        expected = histogram_counter(case['oracle'])
        type_occurrences.update(expected)
        record = dict(id=case['id'], triangulation_id=case['triangulation_id'],
                      input_sha256=case['input_sha256'], oracle_sha256=case['oracle_sha256'],
                      normal_discs=case['normal_discs'], modes={})
        if recheck_oracle:
            observed = oracles[case['triangulation_id']].census(flat(case['coordinates']))
            record['fresh_oracle_match'] = observed == case['oracle']
            if not record['fresh_oracle_match']:
                report['failures'].append(dict(case=case['id'], stage='fresh Regina', observed=observed))
        configurations = [('direct', False, 'fine_wilf'), ('core', True, 'fine_wilf')]
        if index % 10 == 0:
            configurations.append(('direct_aht_control', False, 'aht'))
        for name, reduced, periodic_rule in configurations:
            calls += 1
            mode = dict(reduce_core=reduced, periodic_rule=periodic_rule)
            tick = time.monotonic()
            deadline = tick + timeout

            def check():
                if time.monotonic() >= deadline:
                    raise TimeoutError('audit cooperative wall-clock allowance exhausted')

            try:
                result = normal_topology_spectrum(raw, case['coordinates'],
                    reduce_core=reduced, periodic_rule=periodic_rule,
                    record_certificate=True, check=check)
                mode['produce_seconds'] = time.monotonic() - tick
                mode['status'] = result['status']
                mode['matches_Regina'] = (result['status'] == 'COMPLETE'
                    and histogram_counter(result['topology_spectrum']) == expected)
                if result['status'] == 'COMPLETE':
                    proof = result['certificate']
                    proof_bytes = canonical_bytes(proof)
                    mode['certificate_sha256'] = hashlib.sha256(proof_bytes).hexdigest()
                    mode['certificate_bytes'] = len(proof_bytes)
                    tick = time.monotonic()
                    deadline = tick + timeout
                    mode['certificate_verified'] = verify_normal_topology_spectrum(
                        raw, case['coordinates'], proof, check=check)
                    mode['verify_seconds'] = time.monotonic() - tick
                    mode['orbit_cycles'] = result['stats']['orbit_cycles']
                    mode['queries'] = result['stats']['queries']
                    mode['boundary_transversal_intervals'] = result['stats'].get('boundary_transversal_intervals', 0)
                    mode['query_coordinate_bits'] = result['stats']['query_coordinate_bits']
                    mode['coordinate_divisor'] = proof['coordinate_divisor']
                    mode['vertex_link_multiplicity'] = sum(row['multiplicity'] for row in proof['vertex_links'])
                if not mode['matches_Regina'] or not mode.get('certificate_verified', False):
                    report['failures'].append(dict(case=case['id'], mode=name,
                        expected=case['oracle'], observed=result.get('topology_spectrum'), details=mode))
            except Exception as error:
                mode.update(status='EXCEPTION', error=repr(error), traceback=traceback.format_exc())
                report['failures'].append(dict(case=case['id'], mode=name, details=mode))
            record['modes'][name] = mode
        report['cases'].append(record)
        if (index + 1) % 50 == 0 or index + 1 == len(cases):
            report['elapsed_seconds'] = time.monotonic() - started
            write_json(output, report)
            print(f'audited {index + 1}/{len(cases)} cases, {calls} certificate-producing calls, '
                  f'{len(report["failures"])} failures, {report["elapsed_seconds"]:.2f}s', flush=True)
    after = runtime_hashes()
    report['runtime_sources_unchanged'] = source_before == after
    if not report['runtime_sources_unchanged']:
        report['runtime_sources_after'] = after
        report['failures'].append(dict(stage='runtime source stability',
            changed_files=[path for path in set(source_before) | set(after)
                           if source_before.get(path) != after.get(path)]))
    represented = {case['triangulation_id'] for case in cases}
    modes = [mode for case in report['cases'] for mode in case['modes'].values()]
    report['summary'] = dict(
        cases=len(cases), empty_cases=sum(not case['normal_discs'] for case in cases),
        labeled_triangulations=len(represented),
        triangulation_isomorphism_classes=len({corpus['triangulations'][name]['iso_sig'] for name in represented}),
        tetrahedra_range=[min(corpus['triangulations'][name]['tetrahedra'] for name in represented),
                         max(corpus['triangulations'][name]['tetrahedra'] for name in represented)],
        maximum_normal_discs=max(case['normal_discs'] for case in cases),
        maximum_coordinate=max(case['maximum_coordinate'] for case in cases),
        certificate_calls=calls,
        certificate_matches=sum(mode.get('matches_Regina', False) for mode in modes),
        verified_certificates=sum(mode.get('certificate_verified', False) for mode in modes),
        failures=len(report['failures']),
        distinct_connected_topological_types=len(type_occurrences),
        observed_topological_types=histogram_rows(type_occurrences),
        maximum_orientable_genus=max(((2 - b - chi) // 2 for chi, b, o in type_occurrences if o), default=None),
        maximum_nonorientable_crosscaps=max((2 - b - chi for chi, b, o in type_occurrences if not o), default=None),
        maximum_boundary_circles_on_one_component=max((b for chi, b, o in type_occurrences), default=0),
        total_produce_seconds=sum(mode.get('produce_seconds', 0) for mode in modes),
        total_verify_seconds=sum(mode.get('verify_seconds', 0) for mode in modes),
        maximum_certificate_bytes=max((mode.get('certificate_bytes', 0) for mode in modes), default=0),
        maximum_orbit_cycles=max((mode.get('orbit_cycles', 0) for mode in modes), default=0))
    report['elapsed_seconds'] = time.monotonic() - started
    report['complete'] = len(cases) == len(corpus['cases'])
    report['all_checks_passed'] = not report['failures']
    report['results_sha256'] = digest(report)
    write_json(output, report)
    print(json.dumps(report['summary'], indent=2), flush=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('command', choices=['generate', 'audit', 'run'])
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--recheck-oracle', action='store_true')
    parser.add_argument('--timeout', type=float, default=30.0)
    parser.add_argument('--limit', type=int)
    args = parser.parse_args()
    if args.command != 'generate' and args.output is None:
        parser.error('--output is required for audit and run')
    if args.timeout <= 0:
        parser.error('--timeout must be positive')
    if args.limit is not None and args.limit < 1:
        parser.error('--limit must be positive')
    corpus = generate_corpus(args.corpus) if args.command in ('generate', 'run') else json.loads(args.corpus.read_text())
    if args.command != 'generate':
        report = run_audit(corpus, args.output, recheck_oracle=args.recheck_oracle,
                           timeout=args.timeout, limit=args.limit)
        return 0 if report['all_checks_passed'] else 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
