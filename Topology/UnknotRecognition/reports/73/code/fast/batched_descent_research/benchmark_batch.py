"""Paired fixed-site experiments for simultaneous checked Pachner moves.

Run from fast/: python -m batched_descent_research.benchmark_batch --output ...
This compares the same geometric moves, never different search policies.
Fixture construction, expansion and cohomology seeding are outside timings.
Every timed producer includes its native independent replay.  Standalone
consumers are then timed separately, in alternating paired order.
"""
import argparse
import gc
import json
from pathlib import Path
import platform
import statistics
import time

from fastunknot.pachner_batch import pachner_32_batch
from fastunknot.pachner_batch_verify import verify_pachner_32_batch
from .fixtures import (
    digest, encoded_bytes, inflate_disjoint, sequential_batch, source_fixture,
    verify_sequential_batch,
)


def timed(function):
    calls = [0]
    def tick():
        calls[0] += 1
    gc.collect()
    start = time.perf_counter_ns()
    result = function(tick)
    elapsed = time.perf_counter_ns() - start
    return result, dict(seconds=elapsed / 1e9, callbacks=calls[0])


def run_case(family, count, repeats, evidence_dir=None):
    setup = time.perf_counter()
    initial, initial_h, source = source_fixture(family, count)
    raw, heights, sites, expansions = inflate_disjoint(initial, initial_h, count)
    source.update(expansions=len(expansions), inflated_tetrahedra=len(raw['tetrahedra']),
                  inflated_triangulation_sha256=digest(raw))
    batch = pachner_32_batch(raw, sites, heights)
    regions = batch['certificate']['regions']
    sequential = sequential_batch(raw, heights, regions)
    if (batch['triangulation'] != sequential['triangulation']
            or batch['heights'] != sequential['heights']):
        raise ArithmeticError('batch disagrees with the fixed sequential mathematical state')
    setup_seconds = time.perf_counter() - setup
    producers = {
        'batch': lambda cb: pachner_32_batch(raw, sites, heights, check=cb),
        'sequential': lambda cb: sequential_batch(raw, heights, regions, check=cb),
    }
    consumers = {
        'batch': lambda cb: verify_pachner_32_batch(raw, batch['triangulation'],
                                                    batch['certificate'], heights, check=cb),
        'sequential': lambda cb: verify_sequential_batch(raw, heights,
                                                         sequential['certificate'], check=cb),
    }
    samples = []
    for repeat in range(repeats):
        order = ('batch', 'sequential') if repeat % 2 == 0 else ('sequential', 'batch')
        sample = dict(repetition=repeat, order=list(order), producer={}, verifier={})
        for arm in order:
            answer, sample['producer'][arm] = timed(producers[arm])
            if (answer['triangulation'] != batch['triangulation']
                    or answer['heights'] != batch['heights']):
                raise ArithmeticError('timed producer changed the mathematical result')
        for arm in reversed(order):
            accepted, sample['verifier'][arm] = timed(consumers[arm])
            if not accepted:
                raise ArithmeticError('timed independent consumer rejected retained evidence')
        samples.append(sample)
    summary = {}
    for operation in ('producer', 'verifier'):
        arms = {}
        for arm in producers:
            runs = [sample[operation][arm] for sample in samples]
            callbacks = {run['callbacks'] for run in runs}
            if len(callbacks) != 1:
                raise ArithmeticError('deterministic workload has varying callback count')
            arms[arm] = dict(median_seconds=statistics.median(run['seconds'] for run in runs),
                             callbacks=next(iter(callbacks)))
        arms['speedup'] = arms['sequential']['median_seconds'] / arms['batch']['median_seconds']
        arms['callback_ratio'] = arms['sequential']['callbacks'] / arms['batch']['callbacks']
        summary[operation] = arms
    batch_payload = dict(triangulation=batch['triangulation'], certificate=batch['certificate'])
    sequential_payload = sequential['certificate']
    before_t = len(raw['tetrahedra'])
    size = dict(batch_bytes=len(encoded_bytes(batch_payload)),
                sequential_bytes=len(encoded_bytes(sequential_payload)),
                batch_tetrahedron_rows=before_t-count,
                sequential_tetrahedron_rows=count*before_t-count*(count+1)//2,
                batch_source_preparations=2, batch_target_preparations=1,
                sequential_producer_preparations=8*count,
                batch_verifier_preparations=2,
                sequential_verifier_preparations=4*count)
    size['byte_ratio'] = size['sequential_bytes'] / size['batch_bytes']
    record = dict(family=family, moves=count, source=source,
                  max_input_height_bits=max(abs(x).bit_length() for row in heights for x in row),
                  setup_seconds=setup_seconds, mathematical_state_equal=True,
                  final_triangulation_sha256=digest(batch['triangulation']),
                  final_heights_sha256=digest(batch['heights']),
                  summary=summary, sizes=size, samples=samples)
    if evidence_dir is not None:
        evidence = dict(source=source, initial_triangulation=initial,
                        initial_heights=initial_h, expansions=expansions,
                        before=raw, heights=heights, sites=sites,
                        batch=batch_payload, sequential=sequential_payload)
        path = evidence_dir / f'{family}-{count}.json'
        path.write_text(json.dumps(evidence, separators=(',', ':')) + '\n')
        record['evidence_file'] = path.name
        record['evidence_sha256'] = digest(evidence)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--families', nargs='+', default=['layered', 'unknot', 'trefoil', 'figure_eight'])
    parser.add_argument('--counts', nargs='+', type=int, default=[1, 4, 8, 16, 32, 64])
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--evidence-dir', type=Path)
    args = parser.parse_args()
    if args.repeats < 1 or any(count < 1 for count in args.counts):
        parser.error('positive repetitions and move counts are required')
    if args.evidence_dir is not None:
        args.evidence_dir.mkdir(parents=True, exist_ok=True)
    result = dict(schema='pachner-batch-paired-benchmark-v1',
                  python=platform.python_version(), platform=platform.platform(),
                  repeats=args.repeats,
                  scope='Same fixed disjoint move set; producer includes replay; no search comparison.',
                  cases=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for family in args.families:
        for count in args.counts:
            case = run_case(family, count, args.repeats, args.evidence_dir)
            result['cases'].append(case)
            args.output.write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps(dict(family=family, moves=count,
                tetrahedra=case['source']['inflated_tetrahedra'],
                producer_speedup=case['summary']['producer']['speedup'],
                verifier_speedup=case['summary']['verifier']['speedup'],
                certificate_ratio=case['sizes']['byte_ratio'])), flush=True)


if __name__ == '__main__':
    main()
