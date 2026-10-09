"""Paired supplied-normal-vector benchmarks for the connected topology spectrum.

Run from any directory. All arms record and independently replay certificates.
The coordinates reference first recovers full component vectors (7t weights)
and then obtains the connected topology of each distinct vector. This returns
the same final topological spectrum while computing finer embedding data.
It is not the old aggregate-only surface summary, and none of these timings
is a whole-knot recognition measurement.

The direct A/A arm measures run-order noise. Each case has an interleaved
warmup and seeded shuffled measured rounds. Timings exclude JSON serialization
and fixture construction. Producer and verifier durations are separate.
"""

from collections import Counter
import argparse
from datetime import datetime, timezone
import hashlib
import json
from math import gcd
from pathlib import Path
import platform
import random
import statistics
import sys
import time


FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus


BASELINE = 'eb368edf975695e3e16a8774dcb7846bda0c13a0'
ARMS = ('direct', 'direct_aa', 'reduced', 'coordinates_reference')


def _bytes(value):
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def _digest(value):
    return hashlib.sha256(_bytes(value)).hexdigest()


def _snapshot():
    files = sorted((FAST / 'fastunknot').rglob('*.py'))
    files.extend([Path(__file__).resolve(), FAST / 'normal_orbit_research' / 'fixtures.py',
                  Path(__file__).resolve().parent / 'data' / 'klein_torus.json'])
    return {str(path.relative_to(FAST)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in files}


def _combine(*terms):
    return [[sum(scale * rows[t][j] for scale, rows in terms) for j in range(7)]
            for t in range(len(terms[0][1]))]


def _links(rows):
    # Sum of all vertex-link vectors: one triangle at each local corner.
    return [[1, 1, 1, 1, 0, 0, 0] for _ in rows]


def make_cases(sizes, bit_sizes, quick=False):
    cases = []

    def add(name, family, triangulation, coordinates, parameters):
        common = 0
        for row in coordinates:
            for value in row:
                common = gcd(common, value)
        cases.append(dict(name=name, family=family, triangulation=triangulation,
                          coordinates=coordinates, parameters=parameters,
                          tetrahedra=len(coordinates), coordinate_dimension=7 * len(coordinates),
                          maximum_coordinate_bits=max((v.bit_length() for row in coordinates
                                                       for v in row), default=0),
                          full_coordinate_gcd=common))

    for tetrahedra in sizes:
        triangulation, disk = layered_torus(tetrahedra)
        add(f'meridian_t{tetrahedra}', 'layered_meridian', triangulation, disk,
            dict(tetrahedra=tetrahedra))
    for bits in bit_sizes:
        triangulation, disk = layered_torus(16)
        factor = 1 << bits
        vector = _combine((factor, disk), (factor + 1, _links(disk)))
        add(f'meridian_links_b{bits}', 'large_quadrilateral_content', triangulation, vector,
            dict(exponent_bits=bits, factor=factor, formula='g D + (g+1) L'))
    large_bits = 128 if quick else 4096
    triangulation, _ = layered_torus(1)
    mobius = [[0, 0, 0, 0, 0, 1, 0]]
    for parity in (0, 1):
        factor = (1 << large_bits) + parity
        add(f'mobius_links_{"odd" if parity else "even"}_b{large_bits}',
            'one_sided_with_boundary', triangulation,
            _combine((factor, mobius), (factor + 1, _links(mobius))),
            dict(exponent_bits=large_bits, factor=factor, parity=parity,
                 formula='g M + (g+1) L'))
    fixture = json.loads((Path(__file__).resolve().parent / 'data' / 'klein_torus.json').read_text())
    factor = (1 << large_bits) + 1
    klein = fixture['coordinates']
    add(f'klein_links_odd_b{large_bits}', 'closed_one_sided_zero_signature',
        fixture['triangulation'], _combine((factor, klein), (factor + 1, _links(klein))),
        dict(exponent_bits=large_bits, factor=factor, formula='g K + (g+1) L'))
    triangulation, basis = interior_vertex_torus()
    factor = (1 << large_bits) + 1
    add(f'mobius_sphere_disk_links_b{large_bits}', 'mixed_vertex_links', triangulation,
        _combine((factor, basis['mobius']), (factor + 1, basis['boundary_disk']),
                 (factor + 2, basis['sphere'])),
        dict(exponent_bits=large_bits, factor=factor, formula='g M + (g+1) Ld + (g+2) Ls'))
    return cases


def _row_key(row):
    return row['chi'], row['boundary_components'], not row['orientable']


def _reference_spectrum(records):
    counts = Counter()
    for record in records:
        result = record['topology']
        if encoded_integer(result['components']) != 1:
            raise AssertionError('the coordinate census did not supply one connected component')
        orientable = encoded_integer(result['orientable_components']) == 1
        field = 'genus' if orientable else 'crosscaps'
        counts[encoded_integer(result['euler_characteristic']),
               encoded_integer(result['boundary_components']),
               orientable, encoded_integer(result[field])] += encoded_integer(record['multiplicity'])
    rows = []
    for (chi, boundary, orientable, genus), count in counts.items():
        row = dict(chi=chi, boundary_components=boundary, orientable=orientable,
                   multiplicity=count)
        row['genus' if orientable else 'crosscaps'] = genus
        rows.append(row)
    return sorted(rows, key=_row_key)


def coordinates_reference(triangulation, coordinates, check):
    census = normal_component_census(triangulation, coordinates, mode='coordinates',
                                     record_certificate=True, check=check)
    if census['status'] != 'COMPLETE':
        raise AssertionError('unlimited coordinate census was incomplete')
    records = []
    for component in census['component_histogram']:
        check()
        vector = component['coordinates']
        result = normal_surface_topology(triangulation, vector,
                                         record_certificate=True, check=check)
        if result['status'] != 'COMPLETE':
            raise AssertionError('unlimited connected topology query was incomplete')
        records.append(dict(coordinates=vector, multiplicity=component['multiplicity'],
                            topology=result['certificate']['topology'],
                            certificate=result['certificate'], cycles=result['cycles'],
                            queries=result['queries']))
    spectrum = _reference_spectrum(records)
    certificate = dict(component_census=census['certificate'],
                       connected_topologies=[{key: record[key] for key in
                                              ('coordinates', 'multiplicity', 'certificate')}
                                             for record in records],
                       topology_spectrum=spectrum)
    stats = dict(orbit_cycles=census['stats']['orbit_cycles']
                 + sum(record['cycles'] for record in records),
                 queries=1 + sum(len(record['queries']) for record in records),
                 weight_dimension=census['weight_dimension'],
                 distinct_component_vectors=len(records), census=census['stats'],
                 component_queries=[record['queries'] for record in records])
    return dict(status='COMPLETE', topology_spectrum=spectrum,
                certificate=certificate, stats=stats)


def verify_coordinates_reference(triangulation, coordinates, certificate, check):
    census = certificate['component_census']
    if not verify_normal_component_certificate(triangulation, coordinates, census, check=check):
        return False
    expected = census['summary']['component_histogram']
    supplied = certificate['connected_topologies']
    if len(expected) != len(supplied):
        return False
    records = []
    for component, record in zip(expected, supplied):
        check()
        if (component['coordinates'] != record['coordinates']
                or component['multiplicity'] != record['multiplicity']):
            return False
        if not verify_normal_surface_certificate(triangulation, record['coordinates'],
                                                   record['certificate'], check=check):
            return False
        records.append(dict(topology=record['certificate']['topology'],
                            multiplicity=record['multiplicity']))
    expected_rows = _reference_spectrum(records)
    actual_rows = [{key: value if key == 'orientable' else encoded_integer(value)
                    for key, value in row.items()} for row in certificate['topology_spectrum']]
    return expected_rows == actual_rows


def _run(case, arm, timeout):
    started = time.perf_counter_ns()
    deadline = time.monotonic() + timeout

    def check():
        if time.monotonic() >= deadline:
            raise TimeoutError('per-call wall allowance exhausted')

    phase = 'producer'
    producer_ns = None
    try:
        if arm == 'coordinates_reference':
            result = coordinates_reference(case['triangulation'], case['coordinates'], check)
        else:
            result = normal_topology_spectrum(case['triangulation'], case['coordinates'],
                        reduce_core=(arm == 'reduced'), record_certificate=True, check=check)
        produced = time.perf_counter_ns()
        producer_ns = produced - started
        if result['status'] != 'COMPLETE':
            return dict(status='INCONCLUSIVE', phase=phase, producer_ns=producer_ns,
                        result=result), None
        phase = 'verifier'
        if arm == 'coordinates_reference':
            valid = verify_coordinates_reference(case['triangulation'], case['coordinates'],
                                                   result['certificate'], check)
        else:
            valid = verify_normal_topology_spectrum(case['triangulation'], case['coordinates'],
                                                    result['certificate'], check=check)
        verified = time.perf_counter_ns()
        if not valid:
            raise AssertionError(f'{case["name"]}: {arm} certificate did not replay')
        blob = _bytes(result['certificate'])
        return dict(status='COMPLETE', producer_ns=producer_ns,
                    verifier_ns=verified - produced, total_ns=verified - started,
                    certificate_bytes=len(blob), certificate_sha256=hashlib.sha256(blob).hexdigest(),
                    spectrum_sha256=_digest(result['topology_spectrum']),
                    stats=result['stats']), result
    except TimeoutError as error:
        return dict(status='INCONCLUSIVE', phase=phase, producer_ns=producer_ns,
                    elapsed_ns=time.perf_counter_ns() - started, reason=str(error)), None


def _summary(rounds):
    answer = {}
    for arm in ARMS:
        samples = [row['samples'][arm] for row in rounds]
        done = [sample for sample in samples if sample['status'] == 'COMPLETE']
        record = dict(completed=len(done), attempted=len(samples))
        if done:
            for field in ('producer_ns', 'verifier_ns', 'total_ns', 'certificate_bytes'):
                record[f'median_{field}'] = statistics.median(sample[field] for sample in done)
        answer[arm] = record
    comparisons = [('direct_to_reduced', 'direct', 'reduced'),
                   ('reference_to_direct', 'coordinates_reference', 'direct'),
                   ('reference_to_reduced', 'coordinates_reference', 'reduced'),
                   ('direct_aa_to_direct', 'direct_aa', 'direct')]
    for name, numerator, denominator in comparisons:
        record = {}
        for field in ('producer_ns', 'verifier_ns', 'total_ns'):
            ratios = [row['samples'][numerator][field] / row['samples'][denominator][field]
                      for row in rounds if all(row['samples'][arm]['status'] == 'COMPLETE'
                                               for arm in (numerator, denominator))]
            if ratios:
                record[f'median_paired_{field}_ratio'] = statistics.median(ratios)
        answer[name] = record
    return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--seed', type=int, default=2026100919)
    parser.add_argument('--sizes', nargs='+', type=int, default=[8, 16, 32, 64, 128])
    parser.add_argument('--bit-sizes', nargs='+', type=int, default=[128, 4096, 16384, 32768])
    parser.add_argument('--timeout', type=float, default=90)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--save-proofs', action='store_true')
    args = parser.parse_args()
    if args.rounds < 1 or args.timeout <= 0 or min(args.sizes + args.bit_sizes) < 1:
        parser.error('positive rounds, timeout, sizes and bit-sizes are required')
    if args.quick:
        args.sizes, args.bit_sizes = [8, 32], [128, 4096]
    before = _snapshot()
    rng = random.Random(args.seed)
    destination = args.output.resolve()
    destination.parent.mkdir(parents=True, exist_ok=True)
    proof_root = destination.parent / (destination.stem + '-proofs')
    output = dict(schema='normal-topology-paired-benchmark-v1',
        started_utc=datetime.now(timezone.utc).isoformat(), baseline_commit=BASELINE,
        python=sys.version, platform=platform.platform(), seed=args.seed,
        clock='perf_counter_ns; producer and verifier separate; serialization excluded',
        rounds_per_case=args.rounds, warmup_rounds=1, source_hashes_before=before,
        arms=list(ARMS), cases=[],
        scope='Supplied normal-vector subroutines, with certificate generation and independent replay. '
              'The coordinates reference computes finer component-vector data before classification. '
              'No whole-knot recognition timing, Regina timing, or timing-fit complexity claim.')
    for case in make_cases(args.sizes, args.bit_sizes, quick=args.quick):
        order = list(ARMS)
        rng.shuffle(order)
        record = dict(source=case, source_sha256=_digest(case), warmup=dict(order=order, samples={}),
                      rounds=[])
        expected = None
        proofs_saved = set()
        for number in range(-1, args.rounds):
            if number >= 0:
                order = list(ARMS)
                rng.shuffle(order)
                row = dict(round=number, order=order, samples={})
                record['rounds'].append(row)
            else:
                row = record['warmup']
            for arm in order:
                sample, result = _run(case, arm, args.timeout)
                row['samples'][arm] = sample
                if result is not None:
                    spectrum = result['topology_spectrum']
                    if expected is None:
                        expected = spectrum
                        record['expected_topology_spectrum'] = spectrum
                    elif spectrum != expected:
                        raise AssertionError(f'{case["name"]}: {arm} topological spectrum differs')
                    if args.save_proofs and arm not in proofs_saved:
                        directory = proof_root / case['name']
                        directory.mkdir(parents=True, exist_ok=True)
                        (directory / f'{arm}.json').write_bytes(_bytes(result['certificate']) + b'\n')
                        proofs_saved.add(arm)
        record['summary'] = _summary(record['rounds'])
        output['cases'].append(record)
        destination.write_bytes(_bytes(output) + b'\n')
        summary = record['summary']
        times = {arm: round(summary[arm].get('median_total_ns', 0) / 1e6, 3) for arm in ARMS}
        print(json.dumps(dict(case=case['name'], milliseconds=times,
                              paired_reduced=summary['direct_to_reduced'],
                              paired_dimension=summary['reference_to_direct'])), flush=True)
    after = _snapshot()
    output.update(finished_utc=datetime.now(timezone.utc).isoformat(),
                  source_hashes_after=after, sources_unchanged=(before == after))
    destination.write_bytes(_bytes(output) + b'\n')
    if before != after:
        raise RuntimeError('runtime or benchmark source changed during measurements')


if __name__ == '__main__':
    main()
