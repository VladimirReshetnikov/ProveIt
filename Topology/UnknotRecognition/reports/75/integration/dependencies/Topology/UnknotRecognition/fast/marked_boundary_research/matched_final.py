"""Interleaved final-source moment/one-hot comparison on one native boundary.

Run from fast/: python -m marked_boundary_research.matched_final
There are three paired trials at each of 8, 32, and 128 marks. The first
encoding alternates between pairs and cases: AB/BA/AB, BA/AB/BA, AB/BA/AB.
Each paired trial completes both encodings before starting the next trial;
it never runs all trials of one encoding before switching to the other.

This measures the producer with certificate generation and independent
replay on a validated native graph. Geometry construction, JSON encoding,
hashing, output comparisons, and copying earlier measurements are outside
those timing intervals. No earlier literal/native/small-control run repeats.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import platform
from statistics import median
from time import perf_counter_ns, process_time_ns

from fastunknot.integer_codec import json_safe
from fastunknot.marked_boundary import marked_boundary_order
from fastunknot.marked_boundary_verify import verify_marked_boundary_certificate
from fastunknot.normal_surface_geometry import normal_arc_pairings
from normal_orbit_research.fixtures import layered_torus
from .benchmark import first_half_edge


FAST_ROOT = Path(__file__).resolve().parents[1]
RESEARCH_ROOT = Path(__file__).resolve().parent
ENCODINGS = ('moments', 'one_hot')
SOURCE_FILES = (
    'fastunknot/integer_codec.py',
    'fastunknot/interval_merger.py',
    'fastunknot/interval_orbits.py',
    'fastunknot/interval_orbit_verify.py',
    'fastunknot/weighted_orbits.py',
    'fastunknot/weighted_orbit_verify.py',
    'fastunknot/normal_surface_geometry.py',
    'fastunknot/marked_boundary.py',
    'fastunknot/marked_boundary_verify.py',
    'normal_orbit_research/fixtures.py',
    'marked_boundary_research/benchmark.py',
    'marked_boundary_research/matched_final.py',
)
OUTPUT_FIELDS = ('ports', 'connections', 'cycles', 'unmarked_cycles', 'component_count')


def serialized(value):
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return sha256(serialized(value)).hexdigest()


def source_snapshot():
    return {name: sha256((FAST_ROOT / name).read_bytes()).hexdigest() for name in SOURCE_FILES}


def legacy_snapshot(path):
    """Copy earlier observations verbatim while retaining their source phase."""
    raw_bytes = path.read_bytes()
    old = json.loads(raw_bytes)
    provenance = old.get('measurement_provenance', {})
    if provenance.get('source_phase') != 'before_native_marked_callback_fix':
        raise ValueError('the earlier measurements need their recorded pre-fix provenance')
    numeric_payload = {'rows': old['rows'], 'small_controls': old['small_controls']}
    if digest(numeric_payload) != provenance['numeric_payload_sha256']:
        raise ValueError('earlier numerical observations changed after provenance marking')
    return dict(
        filename=path.name, file_sha256=sha256(raw_bytes).hexdigest(),
        measurement_provenance=provenance,
        scope=old['scope'], repeats=old['repeats'], statistic=old['statistic'],
        environment=old['environment'],
        literal_and_native_rows=[row for row in old['rows'] if row['weight_encoding'] == 'moments'],
        small_controls=old['small_controls'],
        note='These are unchanged earlier observations, not final-source reruns.')


def run_encoding(size, pairings, marks, direction, encoding):
    start_wall, start_cpu = perf_counter_ns(), process_time_ns()
    answer = marked_boundary_order(size, pairings, marks, start_half_edge=direction,
                                   weight_encoding=encoding, record_certificate=True)
    producer_cpu, producer_wall = process_time_ns() - start_cpu, perf_counter_ns() - start_wall
    if answer['status'] != 'COMPLETE':
        raise ArithmeticError('a matched native producer did not complete')
    certificate = answer['certificate']
    start_wall, start_cpu = perf_counter_ns(), process_time_ns()
    accepted = verify_marked_boundary_certificate(size, pairings, marks, certificate,
                                                  start_half_edge=direction,
                                                  weight_encoding=encoding)
    replay_cpu, replay_wall = process_time_ns() - start_cpu, perf_counter_ns() - start_wall
    if not accepted:
        raise ArithmeticError('a matched native certificate failed independent replay')
    output = {field: answer[field] for field in OUTPUT_FIELDS}
    orbit_proof = certificate['weighted_proof']['orbit_proof']
    observation = dict(
        weight_encoding=encoding, weight_dimension=answer['stats']['weight_dimension'],
        producer_seconds=producer_wall / 1e9, replay_seconds=replay_wall / 1e9,
        producer_wall_ns=producer_wall, replay_wall_ns=replay_wall,
        producer_cpu_ns=producer_cpu, replay_cpu_ns=replay_cpu,
        combined_seconds=(producer_wall + replay_wall) / 1e9,
        combined_wall_ns=producer_wall + replay_wall,
        combined_cpu_ns=producer_cpu + replay_cpu,
        certificate_bytes=len(serialized(certificate)),
        output_bytes=len(serialized(output)), orbit_proof_bytes=len(serialized(orbit_proof)),
        output_sha256=digest(output), orbit_proof_sha256=digest(orbit_proof),
        certificate_sha256=digest(certificate),
        trace_events=len(orbit_proof['operations']),
        independently_verified=True)
    return observation, output, orbit_proof, certificate


def case(size, pairings, count, case_index):
    marks = [index * size // count for index in range(count)]
    direction = first_half_edge(pairings, marks[0])
    trials, reference_output, reference_orbits = [], None, None
    certificates = {}
    for trial_index in range(3):
        order = ENCODINGS if (case_index + trial_index) % 2 == 0 else ENCODINGS[::-1]
        observations = []
        for position, encoding in enumerate(order):
            observation, output, orbits, certificate = run_encoding(
                size, pairings, marks, direction, encoding)
            if reference_output is None:
                reference_output, reference_orbits = output, orbits
            # Equality is checked on complete exact objects, not just hashes.
            if output != reference_output or orbits != reference_orbits:
                raise ArithmeticError('matched encodings changed an output or the exact AHT trace')
            if output['component_count'] != 1 or output['cycles'][0]['vertices'] != size:
                raise ArithmeticError('the primitive native meridian was not recovered')
            observation.update(position_in_pair=position, exact_output_agreement=True,
                               exact_orbit_proof_agreement=True)
            observations.append(observation)
            certificates.setdefault(encoding, certificate)
            print(json.dumps(dict(marks=count, trial=trial_index + 1, position=position + 1,
                                  encoding=encoding,
                                  producer_seconds=observation['producer_seconds'],
                                  replay_seconds=observation['replay_seconds'],
                                  trace_events=observation['trace_events']), sort_keys=True), flush=True)
        trials.append(dict(trial=trial_index + 1, encoding_order=list(order),
                           observations=observations))
    summaries = {}
    for encoding in ENCODINGS:
        rows = [row for trial in trials for row in trial['observations']
                if row['weight_encoding'] == encoding]
        summaries[encoding] = dict(
            producer_seconds=median(row['producer_seconds'] for row in rows),
            replay_seconds=median(row['replay_seconds'] for row in rows),
            combined_seconds=median(row['combined_seconds'] for row in rows),
            producer_cpu_seconds=median(row['producer_cpu_ns'] for row in rows) / 1e9,
            replay_cpu_seconds=median(row['replay_cpu_ns'] for row in rows) / 1e9,
            total_producer_seconds=sum(row['producer_wall_ns'] for row in rows) / 1e9,
            total_replay_seconds=sum(row['replay_wall_ns'] for row in rows) / 1e9,
            total_combined_seconds=sum(row['combined_wall_ns'] for row in rows) / 1e9,
            certificate_bytes=rows[0]['certificate_bytes'], output_bytes=rows[0]['output_bytes'],
            orbit_proof_bytes=rows[0]['orbit_proof_bytes'], trace_events=rows[0]['trace_events'])
    return dict(marks=marks, marked_vertices=count, start_half_edge=list(direction),
                trials=trials, medians=summaries,
                producer_speedup=summaries['one_hot']['producer_seconds']
                    / summaries['moments']['producer_seconds'],
                replay_speedup=summaries['one_hot']['replay_seconds']
                    / summaries['moments']['replay_seconds'],
                combined_speedup=summaries['one_hot']['combined_seconds']
                    / summaries['moments']['combined_seconds'],
                exact_output=reference_output, reference_certificates=certificates,
                all_six_outputs_and_orbit_proofs_identical=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=RESEARCH_ROOT / 'measurements_matched_final.json')
    parser.add_argument('--legacy', type=Path, default=RESEARCH_ROOT / 'measurements.json')
    options = parser.parse_args()
    if options.output.resolve() == options.legacy.resolve():
        raise ValueError('the final matched output must not overwrite the earlier measurements')
    earlier = legacy_snapshot(options.legacy)
    code_before = source_snapshot()
    started = datetime.now(timezone.utc).isoformat()
    raw, coordinates = layered_torus(64)
    size, pairings = normal_arc_pairings(raw, coordinates, boundary=True)
    cases = [case(size, pairings, count, index) for index, count in enumerate((8, 32, 128))]
    code_after = source_snapshot()
    if code_before != code_after:
        raise RuntimeError('measured source files changed during the matched experiment')
    result = dict(
        schema='native-marked-boundary-matched-final-v1',
        source_phase='after_native_marked_callback_fix',
        started_utc=started, finished_utc=datetime.now(timezone.utc).isoformat(),
        environment=dict(python=platform.python_version(), platform=platform.platform()),
        source_sha256=code_before, source_unchanged_during_run=True,
        scope='Supplied normal-boundary graph producer and independent replay; not knot recognition',
        timing_policy='Three paired trials per mark count; first arm alternates by trial and case; '
                      'certificate generation is timed, hashing/serialization/geometry are excluded.',
        statistic='Median of three wall-clock observations per encoding; all raw wall/CPU times retained',
        native_source=dict(triangulation=raw, coordinates=coordinates, points=size,
                           pairings=[[p.a, p.b, p.c, p.d, -1 if p.reverse else 1] for p in pairings]),
        cases=cases, earlier_scope_measurements=earlier)
    options.output.parent.mkdir(parents=True, exist_ok=True)
    options.output.write_text(json.dumps(json_safe(result), indent=2) + '\n')
    print(str(options.output), flush=True)


if __name__ == '__main__':
    main()
