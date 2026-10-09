#!/usr/bin/env python3
"""Reproducible paired benchmarks for supplied normal-surface certificates.

All timed public queries produce a certificate and receive one explicit
independent external verification. The ray query's additional internal replay
is deliberately included in generation time. Inputs, serialization, summary
comparisons, and artifact writes are outside the query timers.

The transport cohort reuses one selected basis and one unweighted orbit trace.
Its timers include validated weighted replay and external weighted replay,
but exclude geometry, basis compilation, weight construction and discovery.

Run serially after freezing source files. Default cohorts have one warm-up
and five alternating-order rounds; sizes >=256 use three measured rounds.
Predeclared call and whole-run limits retain explicit incomplete records.
No comparison is reported from fewer complete pairs than its planned rounds.
"""

import argparse
from collections import Counter
from copy import deepcopy
import csv
from datetime import datetime, timezone
import gc
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _arc_system
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from fastunknot.normal_packed_components import (
    normal_packed_component_census, _projected_system,
)
from fastunknot.normal_packed_verify import verify_normal_packed_certificate
from fastunknot.normal_ray_blocks import normal_ray_block_disk_count
from fastunknot.normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate
from fastunknot.normal_support import compile_support
from fastunknot.normal_support_verify import verify_support
from fastunknot.interval_orbits import count_orbits
from fastunknot.weighted_orbits import weighted_histogram_from_orbit_certificate
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from normal_orbit_research.fixtures import layered_torus, boundary_cap, interior_vertex_torus


SEED = 2610092241
BASELINE_COMMIT = '3a90fb34146c915328ab8eac6250cc2514f74ed0'


def compact_bytes(value):
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return hashlib.sha256(compact_bytes(value)).hexdigest()


def source_hashes():
    files = sorted((ROOT / 'fastunknot').rglob('*.py'))
    files += [ROOT / 'normal_orbit_research' / 'fixtures.py', Path(__file__),
              Path(__file__).with_name('source_corpus.json')]
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in files if path.is_file()}


def environment():
    try:
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                                       text=True, stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        head = None
    clock = time.get_clock_info('perf_counter')
    return dict(python=sys.version, executable=sys.executable,
                implementation=platform.python_implementation(), platform=platform.platform(),
                machine=platform.machine(), processor=platform.processor(), cpu_count=os.cpu_count(),
                git_head=head, maintained_baseline_commit=BASELINE_COMMIT,
                perf_counter=dict(resolution=clock.resolution, monotonic=clock.monotonic),
                garbage_collection_enabled=gc.isenabled(),
                thread_environment={key: os.environ[key] for key in
                    ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS') if key in os.environ})


class TimeLimit(RuntimeError):
    pass


class Guard:
    """A sampled cooperative timeout; every callback still increments a counter."""
    def __init__(self, deadline):
        self.deadline, self.calls = deadline, 0

    def __call__(self):
        self.calls += 1
        if (self.calls & 255) == 0:
            self.poll()

    def poll(self):
        if time.perf_counter() >= self.deadline:
            raise TimeLimit('predeclared cooperative time allowance exhausted')


def coordinate_signature(answer):
    histogram = Counter()
    for item in answer['component_histogram']:
        vector = tuple(value for row in item['coordinates'] for value in row)
        histogram[vector] += item['multiplicity']
    return dict(components=answer['components'],
                compressing_disk_components=answer['compressing_disk_components'],
                contains_compressing_disk=answer['contains_compressing_disk'],
                histogram=[dict(vector=list(vector), multiplicity=count)
                           for vector, count in sorted(histogram.items())])


def disc_signature(answer):
    return dict(compressing_disk_components=answer['compressing_disk_components'],
                contains_compressing_disk=answer['contains_compressing_disk'])


def _copies(engines):
    return {engine + '_' + suffix: dict(spec, engine=engine)
            for engine, spec in engines.items() for suffix in ('A', 'B')}


def public_arms(raw, coordinates, category):
    if category == 'coordinates':
        engines = {
            'old_compact': dict(
                generate=lambda check: normal_component_census(raw, coordinates,
                    mode='coordinates', record_certificate=True, check=check),
                verify=lambda proof, check: verify_normal_component_certificate(
                    raw, coordinates, proof, check=check), internal_disc_replays=0),
            'support_vector': dict(
                generate=lambda check: normal_packed_component_census(raw, coordinates,
                    encoding='vector', record_certificate=True, check=check),
                verify=lambda proof, check: verify_normal_packed_certificate(
                    raw, coordinates, proof, check=check), internal_disc_replays=0),
            'support_packed': dict(
                generate=lambda check: normal_packed_component_census(raw, coordinates,
                    encoding='packed', record_certificate=True, check=check),
                verify=lambda proof, check: verify_normal_packed_certificate(
                    raw, coordinates, proof, check=check), internal_disc_replays=0),
        }
        comparisons = [('old_compact_A', 'support_vector_A'),
                       ('old_compact_A', 'support_packed_A'),
                       ('support_vector_A', 'support_packed_A')]
        signature = coordinate_signature
    else:
        engines = {
            'old_disc': dict(
                generate=lambda check: normal_compressing_disk_count(raw, coordinates,
                    record_certificate=True, check=check),
                verify=lambda proof, check: verify_normal_disk_count_certificate(
                    raw, coordinates, proof, check=check), internal_disc_replays=0),
            'ray_disc': dict(
                generate=lambda check: normal_ray_block_disk_count(raw, coordinates,
                    record_certificate=True, check=check),
                verify=lambda proof, check: verify_normal_ray_block_disk_certificate(
                    raw, coordinates, proof, check=check), internal_disc_replays=1),
        }
        comparisons = [('old_disc_A', 'ray_disc_A')]
        signature = disc_signature
    controls = [(engine + '_A', engine + '_B') for engine in engines]
    return _copies(engines), comparisons, controls, signature


def fixtures(sizes):
    cases = []
    for size in sizes:
        raw, coordinates = layered_torus(size)
        cases.append(dict(id=f'fibonacci_{size:04d}', family='fibonacci', size=size,
                          triangulation=raw, coordinates=coordinates,
                          provenance='normal_orbit_research.fixtures.layered_torus'))
    raw, basis = interior_vertex_torus()
    for name, coefficients in (('interior_links', (2, 3, 0)),
                               ('interior_three_way', (3, 2, 5))):
        coordinates = [[sum(coefficient * basis[key][t][i] for coefficient, key in
                            zip(coefficients, ('sphere', 'boundary_disk', 'mobius')))
                        for i in range(7)] for t in range(4)]
        cases.append(dict(id=name, family='overhead_control', size=4,
                          triangulation=deepcopy(raw), coordinates=coordinates,
                          provenance='fixed interior-vertex sphere/disc/Mobius combinations'))
    raw, coordinates = layered_torus(8)
    for _ in range(4):
        raw, coordinates = boundary_cap(raw, coordinates)
    prepared = _prepare(raw, lambda: None)
    roots = sorted(set(prepared['vertex_roots']))
    amounts = {vertex: 2 + i for i, vertex in enumerate(roots)}
    mixed = [[3 * value for value in row] for row in coordinates]
    for t, row in enumerate(mixed):
        for v in range(4):
            row[v] += amounts[prepared['vertex_roots'][4 * t + v]]
    cases.append(dict(id='capped_meridian_links', family='overhead_control', size=len(mixed),
                      triangulation=raw, coordinates=mixed,
                      provenance='8-layer meridian with four boundary caps and unequal vertex links'))
    return cases


def transport_arms(raw, coordinates, check):
    """Prepare identical projected vector/scalar systems and one common trace."""
    prepared = _prepare(raw, check)
    analysed = _coordinates(prepared, coordinates, check)
    support = compile_support(prepared, analysed, check)
    if not verify_support(prepared, analysed, support, check):
        raise AssertionError('transport setup support certificate failed replay')
    systems = {encoding: _projected_system(prepared, analysed, support['selected'], encoding, check)
               for encoding in ('vector', 'packed')}
    vector, packed = systems['vector'], systems['packed']
    if (vector['size'], vector['pairings']) != (packed['size'], packed['pairings']):
        raise AssertionError('transport arms have different orbit problems')
    counted = count_orbits(vector['size'], vector['pairings'], check=check,
                           record_certificate=True)
    if not counted.complete:
        raise AssertionError('uncapped transport setup did not complete')
    trace = counted.certificate
    engines = {}
    for encoding, system in systems.items():
        def generate(check, system=system):
            return weighted_histogram_from_orbit_certificate(system['size'],
                system['pairings'], system['weights'], trace,
                dimension=system['dimension'], check=check, record_certificate=True)

        def verify(proof, check, system=system):
            return verify_weighted_orbit_certificate(system['size'], system['pairings'],
                system['weights'], proof, dimension=system['dimension'], check=check)

        engines['transport_' + encoding] = dict(generate=generate, verify=verify,
                                                internal_disc_replays=0)

    def signature(answer):
        result = []
        for item in answer['histogram']:
            weight = item['weight']
            if answer['certificate']['dimension'] == 1 and len(support['selected']) != 1:
                code = weight[0]
                weight = [(code >> shift) & ((1 << width) - 1)
                          for shift, width in zip(packed['shifts'], packed['widths'])]
            else:
                weight = weight[:len(support['selected'])]
            result.append((tuple(weight), item['orbits']))
        return sorted(result)

    metadata = dict(selected=support['selected'], projection_dimension=len(support['selected']),
                    vector_dimension=vector['dimension'], packed_dimension=packed['dimension'],
                    source_slot_bits=packed['widths'], packed_bits=packed['packed_bits'],
                    orbit_cycles=counted.cycles, orbit_trace_sha256=digest(trace),
                    support_certificate_sha256=digest(support),
                    input_weight_intervals={key: len(system['weights']) for key, system in systems.items()})
    return (_copies(engines), [('transport_vector_A', 'transport_packed_A')],
            [('transport_vector_A', 'transport_vector_B'),
             ('transport_packed_A', 'transport_packed_B')], signature, metadata)


def diagram_case(crossings, check=lambda: None):
    from fastunknot.diagram import Diagram
    from fastunknot.diagram_exterior import diagram_exterior
    from fastunknot.normal_cocycle import rank_one_cocycle_seed
    from fastunknot.normal_support_diagram import (
        certify_diagram_ray_disks, verify_diagram_ray_disk_certificate,
    )
    source = Diagram.from_braid(crossings + 1, list(range(1, crossings + 1)))
    raw = diagram_exterior(source, check=check)
    coordinates = rank_one_cocycle_seed(raw, check=check)['coordinates']
    engines = dict(diagram_ray=dict(
        generate=lambda check: certify_diagram_ray_disks(source, coordinates, check=check),
        verify=lambda proof, check: verify_diagram_ray_disk_certificate(source, proof, check=check),
        internal_disc_replays=2))
    case = dict(id=f'diagram_stabilization_{crossings:03d}', family='diagram_certificate_stage',
                size=len(coordinates), crossings=crossings, triangulation=raw,
                coordinates=coordinates, input_pd=[list(row) for row in source.pd],
                provenance='standard stabilized-circle braid; cocycle discovery outside all timers')
    return case, _copies(engines)


class Runner:
    def __init__(self, args):
        self.args = args
        self.started = time.perf_counter()
        self.deadline = self.started + args.max_seconds if args.max_seconds else float('inf')
        self.output = args.output.resolve()
        self.output.parent.mkdir(parents=True, exist_ok=True)
        self.rng = random.Random(SEED)
        self.sources = source_hashes()
        self.document = dict(schema='normal-support-benchmark-v1',
            started_utc=datetime.now(timezone.utc).isoformat(), environment=environment(),
            command=sys.argv, random_seed=SEED, configuration=vars(args).copy(),
            source_hashes_before=self.sources, cohorts=[], samples=[], summaries=[], exclusions=[],
            status='RUNNING', protocol=dict(
                timers='fresh generation plus one independent external verification',
                ray_internal_replay='included in generation, in addition to external replay',
                input_and_serialization='outside timers',
                source_validation='inside every public-query timer',
                cache_policy='fresh function-local states; process and immutable Python imports retained',
                timeout_polling='one monotonic clock check per 256 callbacks, plus stage boundaries',
                order='seeded shuffled first order, exact reverse in the next round',
                warmups='one complete alternating-arm warm-up cohort, retained but excluded from medians',
                comparability='only complete paired rounds; planned-round minimum required for summaries',
                transport_scope='common basis and trace; geometry, compilation and orbit discovery excluded',
                diagram_scope='optional new-wrapper A/A only; source cocycle discovery excluded'))
        self.document['configuration']['output'] = str(self.output)

    def retain(self, category, value):
        payload = compact_bytes(value)
        code = hashlib.sha256(payload).hexdigest()
        if self.args.proofs:
            path = self.output.parent / category / (code + '.json.gz')
            if not path.is_file():
                path.parent.mkdir(exist_ok=True)
                with path.open('wb') as target:
                    with gzip.GzipFile(fileobj=target, mode='wb', mtime=0) as stream:
                        stream.write(payload)
        return code, len(payload)

    def checkpoint(self):
        self.document['elapsed_seconds'] = time.perf_counter() - self.started
        temporary = self.output.with_suffix('.tmp')
        temporary.write_text(json.dumps(json_safe(self.document), indent=2) + '\n')
        temporary.replace(self.output)

    def measure(self, cohort, arm, spec, round_number, order):
        limit = min(self.deadline, time.perf_counter() + self.args.per_call_seconds)
        guard = Guard(limit)
        sample = dict(cohort=cohort, arm=arm, engine=spec['engine'], round=round_number,
                      warmup=round_number < 0, order=order, external_replays_planned=1,
                      external_replays_completed=0,
                      producer_internal_disc_replays=spec['internal_disc_replays'])
        begin = time.perf_counter_ns()
        produced = None
        try:
            guard.poll()
            answer = spec['generate'](guard)
            produced = time.perf_counter_ns()
            guard.poll()
            if answer.get('status') not in ('COMPLETE', 'UNKNOT'):
                sample['status'] = answer.get('status', 'MISSING_STATUS')
                sample['reason'] = answer.get('reason')
            else:
                valid = spec['verify'](answer['certificate'], guard)
                guard.poll()
                if not valid:
                    raise AssertionError('independent external certificate replay rejected')
                sample['status'] = 'COMPLETE'
                sample['external_replays_completed'] = 1
        except TimeLimit as exc:
            sample.update(status='TIME_LIMIT', reason=str(exc))
            answer = None
        except Exception as exc:
            sample.update(status='ERROR', reason=type(exc).__name__ + ': ' + str(exc))
            answer = None
        finished = time.perf_counter_ns()
        sample.update(total_ns=finished - begin, checkpoints=guard.calls,
                      generation_ns=None if produced is None else produced - begin,
                      external_verify_ns=None if produced is None else finished - produced)
        if answer is not None:
            sample['statistics'] = answer.get('stats', {})
            for key in ('weight_dimension', 'projection_dimension', 'packed_bits',
                        'support_size', 'maximum_coordinate_bits', 'normal_points', 'normal_disks'):
                if key in answer:
                    sample[key] = answer[key]
            if 'certificate' in answer:
                code, length = self.retain('certificates', answer['certificate'])
                sample.update(certificate_sha256=code, certificate_json_bytes=length)
        self.document['samples'].append(sample)
        return sample, answer

    def summarize(self, cohort, arms, comparisons, controls, rounds):
        samples = [sample for sample in self.document['samples']
                   if sample['cohort'] == cohort and not sample['warmup']]
        lookup = {(sample['round'], sample['arm']): sample for sample in samples}
        for old, new in comparisons + controls:
            pairs = [(lookup.get((i, old)), lookup.get((i, new))) for i in range(rounds)]
            complete = [(a, b) for a, b in pairs
                        if a and b and a['status'] == b['status'] == 'COMPLETE']
            row = dict(cohort=cohort, numerator_arm=old, denominator_arm=new,
                       control=(old, new) in controls, planned_pairs=rounds,
                       complete_pairs=len(complete), reported=len(complete) == rounds)
            if row['reported']:
                ratios = [a['total_ns'] / b['total_ns'] for a, b in complete]
                row.update(paired_total_ratio_median=statistics.median(ratios),
                           paired_total_ratio_min=min(ratios), paired_total_ratio_max=max(ratios))
                for side, entries in (('numerator', [a for a, _ in complete]),
                                      ('denominator', [b for _, b in complete])):
                    for field in ('total_ns', 'generation_ns', 'external_verify_ns'):
                        row[side + '_' + field + '_median'] = statistics.median(item[field] for item in entries)
            self.document['summaries'].append(row)

    def cohort(self, case, category, arms, comparisons, controls, signature, extra=None):
        key = case['id'] + ':' + category
        rounds = self.args.large_rounds if case['size'] >= self.args.large_threshold else self.args.rounds
        flat = [value for row in case['coordinates'] for value in row]
        input_hash, input_bytes = self.retain('inputs', case)
        metadata = dict(id=key, case=case['id'], category=category, family=case['family'],
                        tetrahedra=len(case['coordinates']), source_positive_coordinates=sum(bool(v) for v in flat),
                        source_maximum_bits=max((v.bit_length() for v in flat), default=0),
                        source_total_coordinate_bits=sum(v.bit_length() for v in flat),
                        input_sha256=input_hash, input_json_bytes=input_bytes,
                        planned_rounds=rounds, planned_warmups=1, arms=list(arms), status='RUNNING')
        if extra:
            metadata.update(extra)
        self.document['cohorts'].append(metadata)
        if time.perf_counter() >= self.deadline:
            metadata['status'] = 'NOT_STARTED_GLOBAL_LIMIT'
            self.checkpoint()
            return
        expected, order, stopped = None, list(arms), False
        for round_number in range(-1, rounds):
            if round_number == -1 or round_number % 2 == 0:
                self.rng.shuffle(order)
            else:
                order.reverse()
            for position, arm in enumerate(order):
                if time.perf_counter() >= self.deadline:
                    metadata['status'] = 'GLOBAL_LIMIT'
                    stopped = True
                    break
                sample, answer = self.measure(key, arm, arms[arm], round_number, position)
                if sample['status'] == 'COMPLETE':
                    observed = digest(signature(answer))
                    sample['answer_sha256'] = observed
                    if expected is None:
                        expected = observed
                    elif expected != observed:
                        sample.update(status='ERROR', reason='cross-arm or repeated-run answer differs')
                if sample['status'] != 'COMPLETE':
                    metadata['status'] = ('WARMUP_' if round_number < 0 else '') + sample['status']
                    stopped = True
                    break
            self.checkpoint()
            if stopped:
                break
        if not stopped:
            metadata['status'] = 'COMPLETE'
        metadata['answer_sha256'] = expected
        self.summarize(key, arms, comparisons, controls, rounds)
        self.checkpoint()
        print(key, metadata['status'], 'elapsed', round(time.perf_counter() - self.started, 3), flush=True)

    def finish(self):
        after = source_hashes()
        self.document['source_hashes_after'] = after
        self.document['sources_unchanged'] = after == self.sources
        errors = [sample for sample in self.document['samples'] if sample['status'] == 'ERROR']
        self.document['status'] = ('ERROR' if errors or after != self.sources else
                                   'COMPLETE' if all(row['status'] == 'COMPLETE'
                                                     for row in self.document['cohorts']) else
                                   'PARTIAL_PREDECLARED_LIMITS')
        self.document['finished_utc'] = datetime.now(timezone.utc).isoformat()
        self.checkpoint()
        fields = ('cohort', 'arm', 'engine', 'round', 'warmup', 'order', 'status', 'total_ns',
                  'generation_ns', 'external_verify_ns', 'checkpoints', 'external_replays_planned',
                  'external_replays_completed',
                  'producer_internal_disc_replays', 'weight_dimension', 'projection_dimension',
                  'packed_bits', 'certificate_json_bytes', 'certificate_sha256', 'answer_sha256', 'reason')
        with self.output.with_suffix('.csv').open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=fields, extrasaction='ignore', lineterminator='\n')
            writer.writeheader()
            writer.writerows(self.document['samples'])
        summary_fields = sorted({key for row in self.document['summaries'] for key in row})
        if summary_fields:
            with self.output.with_name(self.output.stem + '_summary.csv').open('w', newline='') as stream:
                writer = csv.DictWriter(stream, fieldnames=summary_fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(self.document['summaries'])
        print(str(self.output), self.document['status'], flush=True)
        return 1 if self.document['status'] == 'ERROR' else 0


def integers(text):
    return [int(value) for value in text.split(',') if value]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sizes', type=integers, default=integers('8,16,32,64,128,256,512'))
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--large-rounds', type=int, default=3)
    parser.add_argument('--large-threshold', type=int, default=256)
    parser.add_argument('--max-comparison-size', type=int, default=256,
                        help='larger Fibonacci fixtures run new ray A/A capacity measurements only')
    parser.add_argument('--per-call-seconds', type=float, default=12.0)
    parser.add_argument('--max-seconds', type=float, default=300.0,
                        help='zero removes the whole-run deadline')
    parser.add_argument('--diagrams', type=integers, default=[],
                        help='optional source-bound new-wrapper A/A stage, e.g. 1,4,8,16,32')
    parser.add_argument('--proofs', action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('results') / 'benchmark_20261009.json')
    args = parser.parse_args()
    if (args.rounds < 5 or args.large_rounds < 3 or args.large_threshold < 1
            or args.max_comparison_size < 1
            or args.per_call_seconds <= 0 or args.max_seconds < 0
            or any(size < 1 for size in args.sizes + args.diagrams)):
        parser.error('at least five ordinary/three large rounds and positive sizes/allowances required')
    runner = Runner(args)
    cases = fixtures(args.sizes)
    # Interleave the small negative controls before large Fibonacci cases so a
    # global limit cannot preferentially omit measured overhead cases.
    controls = [case for case in cases if case['family'] == 'overhead_control']
    fibonacci = [case for case in cases if case['family'] == 'fibonacci']
    ordered = fibonacci[:2] + controls + fibonacci[2:]
    for case in ordered:
        if case['family'] == 'fibonacci' and case['size'] > args.max_comparison_size:
            runner.document['exclusions'].append(dict(case=case['id'],
                omitted=['old coordinate comparison', 'old disc-count comparison'],
                reason='predeclared --max-comparison-size; new ray capacity/A/A cohort retained'))
            arms, _, _, signature = public_arms(case['triangulation'], case['coordinates'], 'discs')
            arms = {key: value for key, value in arms.items() if value['engine'] == 'ray_disc'}
            runner.cohort(case, 'ray_capacity', arms, [], [('ray_disc_A', 'ray_disc_B')], signature,
                          dict(scope='new ray count capacity and A/A only; no old/new speedup ratio'))
            continue
        for category in ('coordinates', 'discs'):
            arms, comparisons, aa, signature = public_arms(
                case['triangulation'], case['coordinates'], category)
            runner.cohort(case, category, arms, comparisons, aa, signature)
        if case['family'] == 'overhead_control' and time.perf_counter() < runner.deadline:
            started = time.perf_counter()
            guard = Guard(min(runner.deadline, started + args.per_call_seconds))
            try:
                arms, comparisons, aa, signature, metadata = transport_arms(
                    case['triangulation'], case['coordinates'], guard)
            except TimeLimit:
                runner.document['cohorts'].append(dict(id=case['id'] + ':transport',
                    category='transport', case=case['id'], status='SETUP_TIME_LIMIT'))
                continue
            metadata['excluded_setup_seconds'] = time.perf_counter() - started
            runner.cohort(case, 'transport', arms, comparisons, aa, signature, metadata)
    for crossings in args.diagrams:
        if time.perf_counter() >= runner.deadline:
            break
        started = time.perf_counter()
        guard = Guard(min(runner.deadline, started + args.per_call_seconds))
        try:
            case, arms = diagram_case(crossings, guard)
        except TimeLimit:
            runner.document['cohorts'].append(dict(id=f'diagram_stabilization_{crossings:03d}',
                category='diagram_certificate_stage', crossings=crossings, status='SETUP_TIME_LIMIT'))
            continue
        runner.cohort(case, 'diagram_certificate_stage', arms, [],
                      [('diagram_ray_A', 'diagram_ray_B')],
                      lambda answer: dict(status=answer['status'],
                          compressing_disk_components=answer['compressing_disk_components']),
                      dict(excluded_cocycle_discovery_seconds=time.perf_counter() - started,
                           scope='new source-bound wrapper A/A; no automatic-search speedup comparison'))
    return runner.finish()


if __name__ == '__main__':
    raise SystemExit(main())
