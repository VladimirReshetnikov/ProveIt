#!/usr/bin/env python3
"""Replay the retained research evidence without producers or surface search.

From the supplied ``fast`` directory, run::

    python support_research/replay_evidence.py

Only the Python standard library and the packaged proof checkers are needed.
Every gzip input/certificate is SHA256-checked against its content-addressed
filename and the benchmark references *before* its JSON is parsed. The
benchmark's frozen source manifest is also checked. These hashes establish
consistency with the supplied manifest, not authenticity of that manifest.

Repeated A/A and timing-round proofs are deduplicated. Transport-only proofs
are reconstructed from the stored source geometry and the selected kernel
found in a retained packed certificate; no basis compiler or weight producer
is called. Their orbit-trace and kernel digests are checked against the cohort
metadata. If the kernel is absent, that transport record is explicitly skipped.
The optional sample_certificates.json is replayed when present; its observed
file digest is reported, since it has no separate benchmark digest reference.

This checks mathematical evidence and answer digests, not elapsed-time claims
or an exhaustive search for a normal surface. Exit status is 0 for complete
acceptance, 1 for a failure, and 2 for otherwise valid but skipped evidence.
"""

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import platform
import re
import sys
import time

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

# These are checkers and shared finite source representations. In particular,
# do not import benchmark.py, fixtures, the support compiler, or weight builders.
from fastunknot.diagram import Diagram
from fastunknot.integer_codec import certificate_equal, encoded_integer, json_safe
from fastunknot.normal_component_geometry import disk_corner_intervals
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
from fastunknot.normal_packed_verify import verify_normal_packed_certificate
from fastunknot.normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate
from fastunknot.normal_support_diagram import verify_diagram_ray_disk_certificate
from fastunknot.normal_support_verify import verify_support
from fastunknot.normal_surface_geometry import _arc_system, _coordinates, _prepare
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


class SkippedEvidence(Exception):
    """A retained transcript lacks the data needed for independent replay."""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    payload = json.dumps(json_safe(value), sort_keys=True,
                         separators=(',', ':')).encode()
    return hashlib.sha256(payload).hexdigest()


def load_addressed(directory, expected_lengths):
    """Check bytes first; parse only after their expected hash is established."""
    present = {path.name[:-8]: path for path in directory.glob('*.json.gz')}
    require(set(expected_lengths) <= set(present),
            'missing retained files: ' + ', '.join(sorted(set(expected_lengths) - set(present))))
    loaded, records = {}, []
    for code, path in sorted(present.items()):
        require(re.fullmatch('[0-9a-f]{64}', code) is not None,
                'invalid content-addressed filename: ' + path.name)
        payload = gzip.decompress(path.read_bytes())
        require(hashlib.sha256(payload).hexdigest() == code,
                'decompressed SHA256 mismatch: ' + path.name)
        if code in expected_lengths:
            require(expected_lengths[code] == {len(payload)},
                    'benchmark byte count mismatch: ' + path.name)
        loaded[code] = json.loads(payload)
        records.append(dict(sha256=code, decompressed_bytes=len(payload),
                            referenced=code in expected_lengths))
    return loaded, records


def check_source_manifest(document):
    before, after = document['source_hashes_before'], document['source_hashes_after']
    require(document.get('sources_unchanged') is True and before == after,
            'benchmark did not retain an unchanged source manifest')
    for name, expected in sorted(before.items()):
        path = (FAST / name).resolve()
        require(path.is_relative_to(FAST), 'source manifest path escapes fast directory')
        require(path.is_file(), 'missing frozen source: ' + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected,
                'frozen source SHA256 mismatch: ' + name)
    return dict(status='ACCEPTED', checked_files=len(before),
                source_manifest_sha256=digest(before))


def coordinate_signature(summary):
    grouped = Counter()
    for item in summary['component_histogram']:
        vector = tuple(encoded_integer(value) for row in item['coordinates'] for value in row)
        grouped[vector] += encoded_integer(item['multiplicity'])
    count = encoded_integer(summary['compressing_disk_components'])
    return dict(components=encoded_integer(summary['components']),
                compressing_disk_components=count,
                contains_compressing_disk=bool(count),
                histogram=[dict(vector=list(vector), multiplicity=multiplicity)
                           for vector, multiplicity in sorted(grouped.items())])


def transport_signature(case, proof, cohort, engine, kernels):
    """Rebuild selected weights independently from the normal corner geometry."""
    require(engine in ('transport_vector', 'transport_packed'),
            'weighted proof has no recognized transport encoding')
    kernel_hash = cohort.get('support_certificate_sha256')
    if kernel_hash not in kernels:
        raise SkippedEvidence('transport support kernel is absent from retained packed proofs; '
                              'no producer/compiler fallback is permitted')
    kernel = kernels[kernel_hash]
    prepared = _prepare(case['triangulation'], lambda: None)
    analysed = _coordinates(prepared, case['coordinates'], lambda: None)
    require(verify_support(prepared, analysed, kernel), 'transport support kernel rejected')
    selected = [encoded_integer(value) for value in kernel['selected']]
    require(selected == [encoded_integer(value) for value in cohort['selected']],
            'transport selected coordinates differ from retained kernel')
    source = [value for row in analysed['rows'] for value in row]
    widths = [source[index].bit_length() for index in selected]
    require(cohort['source_slot_bits'] == widths and cohort['packed_bits'] == sum(widths),
            'transport slot metadata differs from source coordinates')
    require(cohort['projection_dimension'] == len(selected),
            'transport projection dimension differs from retained kernel')
    packed = engine == 'transport_packed'
    dimension = 1 if packed else max(1, len(selected))
    require(cohort['packed_dimension' if packed else 'vector_dimension'] == dimension,
            'transport weight dimension mismatch')
    factors, capacity = [], 1
    for width in widths:
        factors.append(capacity)
        capacity *= 1 << width
    offsets, total = {}, 0
    for edge, count in sorted(analysed['weights'].items()):
        offsets[edge] = total
        total += count
    size, pairings = _arc_system(prepared, analysed, check=lambda: None)
    require(size == total, 'transport normal edge universe mismatch')
    positions = {index: j for j, index in enumerate(selected)}
    weights = []
    for index, lo, hi in disk_corner_intervals(prepared, analysed, offsets, lambda: None):
        if index in positions:
            j = positions[index]
            value = [factors[j]] if packed else [int(k == j) for k in range(dimension)]
            weights.append((lo, hi, value))
    require(cohort['input_weight_intervals']['packed' if packed else 'vector'] == len(weights),
            'transport weight-interval metadata mismatch')
    require(digest(proof['orbit_proof']) == cohort['orbit_trace_sha256'],
            'transport orbit trace differs from the retained common-trace digest')
    require(verify_weighted_orbit_certificate(size, pairings, weights, proof,
                                             dimension=dimension),
            'independent weighted transport replay rejected')
    result, totals = [], [0] * len(selected)
    for item in proof['histogram']:
        count = encoded_integer(item['orbits'])
        weight = [encoded_integer(value) for value in item['weight']]
        if packed:
            remaining, projected = weight[0], []
            require(0 <= remaining < capacity, 'transport packed code exceeds source box')
            for width in widths:
                remaining, digit = divmod(remaining, 1 << width)
                projected.append(digit)
            require(remaining == 0, 'transport packed code has unused high bits')
        else:
            projected = weight[:len(selected)]
        require(all(0 <= value <= source[index] for index, value in zip(selected, projected)),
                'transport coordinate exceeds source coordinate')
        for j, value in enumerate(projected):
            totals[j] += count * value
        result.append((tuple(projected), count))
    require(totals == [source[index] for index in selected],
            'transport histogram does not reconstruct selected source counts')
    return sorted(result)


def replay(case, proof, cohort, engine, kernels):
    raw, coordinates, schema = case['triangulation'], case['coordinates'], proof['schema']
    expected_schema = {
        'old_compact': ('normal-component-census-v1', 'normal-component-census-v2'),
        'old_disc': ('normal-disc-count-v1',),
        'support_vector': ('normal-packed-components-v1',),
        'support_packed': ('normal-packed-components-v1',),
        'ray_disc': ('normal-ray-block-disks-v1',),
        'diagram_ray': ('diagram-ray-disks-v1',),
        'transport_vector': ('weighted-interval-orbits-v1',),
        'transport_packed': ('weighted-interval-orbits-v1',),
    }
    require(engine in expected_schema and schema in expected_schema[engine],
            'certificate schema and benchmark engine disagree')
    if schema in ('normal-component-census-v1', 'normal-component-census-v2'):
        require(verify_normal_component_certificate(raw, coordinates, proof),
                'independent normal component replay rejected')
        return coordinate_signature(proof['summary'])
    if schema == 'normal-packed-components-v1':
        require(proof['encoding'] == ('vector' if engine == 'support_vector' else 'packed'),
                'packed proof encoding and benchmark engine disagree')
        require(verify_normal_packed_certificate(raw, coordinates, proof),
                'independent support/packed replay rejected')
        return coordinate_signature(proof['summary'])
    if schema == 'normal-disc-count-v1':
        require(verify_normal_disk_count_certificate(raw, coordinates, proof),
                'independent maintained disc-count replay rejected')
    elif schema == 'normal-ray-block-disks-v1':
        require(verify_normal_ray_block_disk_certificate(raw, coordinates, proof),
                'independent ray-block replay rejected')
    elif schema == 'diagram-ray-disks-v1':
        require(proof['triangulation'] == raw and proof['coordinates'] == coordinates,
                'diagram certificate differs from retained triangulation or coordinates')
        source = Diagram.from_pd(case['input_pd'])
        require(verify_diagram_ray_disk_certificate(source, proof),
                'independent source-bound diagram replay rejected')
        return dict(status='UNKNOT', compressing_disk_components=
                    encoded_integer(proof['disc_certificate']['compressing_disk_components']))
    elif schema == 'weighted-interval-orbits-v1':
        return transport_signature(case, proof, cohort, engine, kernels)
    count = encoded_integer(proof['compressing_disk_components'])
    return dict(compressing_disk_components=count, contains_compressing_disk=bool(count))


def replay_archive(benchmark_path, sample_path):
    benchmark_bytes = benchmark_path.read_bytes()
    document = json.loads(benchmark_bytes)
    require(document['schema'] == 'normal-support-benchmark-v1', 'unknown benchmark schema')
    report = dict(benchmark_sha256=hashlib.sha256(benchmark_bytes).hexdigest(),
                  benchmark_status=document['status'], source_check=check_source_manifest(document))
    cohorts = {row['id']: row for row in document['cohorts']}
    require(len(cohorts) == len(document['cohorts']), 'duplicate benchmark cohort identifiers')
    input_lengths, proof_lengths = defaultdict(set), defaultdict(set)
    for row in cohorts.values():
        if 'input_sha256' in row:
            input_lengths[row['input_sha256']].add(row['input_json_bytes'])
    groups = {}
    for sample in document['samples']:
        if 'certificate_sha256' not in sample:
            require(sample['status'] != 'COMPLETE', 'complete benchmark sample has no certificate')
            continue
        cohort = cohorts[sample['cohort']]
        code = sample['certificate_sha256']
        proof_lengths[code].add(sample['certificate_json_bytes'])
        key = code, cohort['input_sha256'], sample['engine'], cohort['id']
        groups.setdefault(key, []).append(sample)
    inputs, input_inventory = load_addressed(benchmark_path.parent / 'inputs', input_lengths)
    proofs, proof_inventory = load_addressed(benchmark_path.parent / 'certificates', proof_lengths)
    report['integrity'] = dict(status='ACCEPTED', inputs=input_inventory,
                               certificates=proof_inventory)
    # A transport cohort records the hash of its selected support kernel. That
    # exact kernel is retained inside both public packed/vector certificates.
    kernels = {digest(proof['support_kernel']): proof['support_kernel']
               for proof in proofs.values() if proof.get('schema') == 'normal-packed-components-v1'}
    results = []
    for (code, input_code, engine, cohort_id), samples in sorted(groups.items()):
        proof, case, cohort = proofs[code], inputs[input_code], cohorts[cohort_id]
        entry = dict(certificate_sha256=code, input_sha256=input_code,
                     schema=proof.get('schema'), engine=engine, cohort=cohort_id,
                     represented_samples=len(samples))
        begin = time.perf_counter()
        try:
            require(case['id'] == cohort['case'], 'cohort points to a different retained case')
            signature = replay(case, proof, cohort, engine, kernels)
            answer_hash = digest(signature)
            for sample in samples:
                if sample.get('status') == 'COMPLETE':
                    require(sample.get('answer_sha256') == answer_hash,
                            'replayed answer differs from benchmark sample digest')
            require(cohort.get('answer_sha256') == answer_hash,
                    'replayed answer differs from benchmark cohort digest')
            entry.update(status='ACCEPTED', answer_sha256=answer_hash)
        except SkippedEvidence as exc:
            entry.update(status='SKIPPED', reason=str(exc))
        except Exception as exc:
            entry.update(status='REJECTED', reason=type(exc).__name__ + ': ' + str(exc))
        entry['replay_seconds'] = time.perf_counter() - begin
        results.append(entry)
    for code in sorted(set(proofs) - set(proof_lengths)):
        results.append(dict(certificate_sha256=code, schema=proofs[code].get('schema'),
                            status='SKIPPED', represented_samples=0,
                            reason='unreferenced certificate has no retained benchmark source association'))
    report['benchmark_replays'] = results
    report['benchmark_counts'] = dict(
        cohorts=len(cohorts), timing_samples=len(document['samples']),
        distinct_inputs=len(inputs), distinct_certificates=len(proofs),
        replay_associations=len(results), statuses=dict(Counter(row['status'] for row in results)),
        represented_samples=sum(row['represented_samples'] for row in results
                                if row['status'] == 'ACCEPTED'),
        schemas=dict(Counter(row['schema'] for row in results if row['status'] == 'ACCEPTED')))
    report['sample_replays'] = replay_samples(sample_path) if sample_path else dict(status='NOT_REQUESTED')
    return report


def replay_samples(path):
    if not path.is_file():
        return dict(status='ABSENT', reason='optional sample_certificates.json was not supplied')
    payload = path.read_bytes()
    cases = json.loads(payload)
    require(type(cases) is list, 'sample certificate bundle must be a list')
    results = []
    for case in cases:
        for key, engine in (('packed_certificate', 'support_packed'), ('ray_certificate', 'ray_disc')):
            if key not in case:
                continue
            proof = case[key]
            entry = dict(case=case['id'], schema=proof.get('schema'),
                         certificate_sha256=digest(proof))
            try:
                replay(case, proof, {}, engine, {})
                entry['status'] = 'ACCEPTED'
            except Exception as exc:
                entry.update(status='REJECTED', reason=type(exc).__name__ + ': ' + str(exc))
            results.append(entry)
    return dict(status='REJECTED' if any(row['status'] != 'ACCEPTED' for row in results) else 'ACCEPTED',
                file_sha256=hashlib.sha256(payload).hexdigest(), cases=len(cases),
                certificates=len(results), statuses=dict(Counter(row['status'] for row in results)),
                replays=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmark', type=Path,
                        default=Path(__file__).with_name('results') / 'benchmark_20261009.json')
    parser.add_argument('--output', type=Path,
                        help='default: evidence_replay.json beside the benchmark')
    parser.add_argument('--skip-samples', action='store_true',
                        help='omit optional sample_certificates.json in the benchmark directory')
    args = parser.parse_args()
    started = time.perf_counter()
    report = dict(schema='normal-support-evidence-replay-v1',
                  started_utc=datetime.now(timezone.utc).isoformat(),
                  python=platform.python_version(), replay_script_sha256=
                  hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='independent source-bound proof replay and content integrity; '
                        'no producers, basis compilation, fixtures, surface search, or timing reproduction')
    try:
        samples = None if args.skip_samples else args.benchmark.with_name('sample_certificates.json')
        report.update(replay_archive(args.benchmark, samples))
        statuses = report['benchmark_counts']['statuses']
        rejected = statuses.get('REJECTED', 0) or report['sample_replays']['status'] == 'REJECTED'
        code = 1 if rejected else 2 if statuses.get('SKIPPED', 0) else 0
        report['status'] = ('ACCEPTED', 'REJECTED', 'PARTIAL')[code]
    except Exception as exc:
        code = 1
        report.update(status='REJECTED', reason=type(exc).__name__ + ': ' + str(exc))
    report['elapsed_seconds'] = time.perf_counter() - started
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    output = args.output or args.benchmark.with_name('evidence_replay.json')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('status', 'benchmark_counts', 'reason')
                      if key in report}, sort_keys=True))
    if 'sample_replays' in report:
        print('Optional sample certificates:', report['sample_replays'].get('statuses',
                                                                          report['sample_replays']['status']))
    print(output)
    return code


if __name__ == '__main__':
    raise SystemExit(main())
