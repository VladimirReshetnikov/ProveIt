"""Paired full assembly benchmarks and separate binary-sheet scaling queries.

The expanded control is an independent explicit lifted-graph algorithm, not
another compressed normal-surface method.  No measurement is knot recognition.
All inputs are valid geometric cover presentations.  Shuffled A/A controls and
one excluded warmup are retained.  Serialization is measured separately by size,
outside the preparation and query timers.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.integer_codec import json_safe
from fastunknot.surface_gluing import GluedCoverIndex, verify_gauge_certificate
from gluing_research.fixtures import annulus_chain, genus_two, klein_seam, projective_cap
from gluing_research.oracle import compressed_records, expanded_assembly


def timed(call, repeats=1):
    start = perf_counter()
    results = [call() for _ in range(repeats)]
    return results, (perf_counter() - start) / repeats


def metadata():
    paths = ['fastunknot/surface_gluing.py', 'fastunknot/surface_cover.py',
             'gluing_research/benchmark.py', 'gluing_research/oracle.py',
             'gluing_research/fixtures.py']
    try:
        base_commit = subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=FAST, text=True,
            stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        base_commit = None  # Standalone research archives need no git checkout.
    return dict(utc=datetime.now(timezone.utc).isoformat(), python=sys.version,
                platform=platform.platform(),
                base_commit=base_commit,
                source_sha256={path: hashlib.sha256((FAST / path).read_bytes()).hexdigest()
                               for path in paths})


def expansion_cases():
    return [
        ('klein_even_256', klein_seam(256, 0)),
        ('klein_even_4096', klein_seam(4096, 0)),
        ('klein_even_65536', klein_seam(65536, 0)),
        ('torus_65536', klein_seam(65536, 1)),
        ('projective_cap_16384', projective_cap(16384, 0)),
        ('genus_two_16384', genus_two(16384)),
        ('chain8_4096', annulus_chain(4096, 8, 1)),
    ]


def expansion_benchmark(rounds, rng):
    records = []
    for name, raw in expansion_cases():
        reference = GluedCoverIndex(raw).summary
        expected = compressed_records(reference)
        samples, execution_order = {'compressed': [], 'control': [], 'expanded': []}, []
        repeats = dict(compressed=100, control=100, expanded=1)
        for iteration in range(-1, rounds):
            order = list(samples)
            rng.shuffle(order)
            execution_order.append(dict(round=iteration, order=order))
            for arm in order:
                call = ((lambda: expanded_assembly(raw)) if arm == 'expanded'
                        else (lambda: GluedCoverIndex(raw).summary))
                results, seconds = timed(call, repeats[arm])
                for result in results:
                    actual = result['records'] if arm == 'expanded' else compressed_records(result)
                    if actual != expected:
                        raise AssertionError((name, arm, 'topology mismatch'))
                if iteration >= 0:
                    samples[arm].append(seconds)
                del results, result, actual
        medians = {arm: median(values) for arm, values in samples.items()}
        records.append(dict(name=name, input=raw, samples_seconds=samples,
                            queries_per_sample=repeats,
                            execution_order=execution_order, medians_seconds=medians,
                            expanded_over_compressed=medians['expanded'] / medians['compressed'],
                            control_over_compressed=medians['control'] / medians['compressed'],
                            expanded_sheet_vertices=raw['sheets'] * len(raw['pieces']),
                            family_records=sum(len(c['families']) for c in reference['base_components']),
                            output_bytes=len(json.dumps(json_safe(reference)).encode()),
                            topology=[dict(base=c['base_surface'], families=c['families'])
                                      for c in reference['base_components']]))
        print(f"{name}: {medians['compressed']:.6f}s compressed, "
              f"{medians['expanded']:.6f}s expanded", flush=True)
    return records


def binary_benchmark(rounds, rng):
    records = []
    for bits in (64, 1024, 4096, 16384):
        for count in (1, 8, 64):
            raw = annulus_chain(1 << bits, count, 1)
            index = GluedCoverIndex(raw)
            certificate = index.gauge_certificate
            marks = [(i % count, ((i + 1) * ((1 << bits) // 137)) % (1 << bits))
                     for i in range(32)]
            expected_signature = index.marked_signature(0, 0, marks)
            samples = {arm: [] for arm in ('prepare', 'prepare_control', 'replay',
                                          'marked', 'marked_control')}
            repeats = {arm: (128 if arm.startswith('marked') else max(16, 128 // count))
                       for arm in samples}
            execution_order = []
            for iteration in range(-1, rounds):
                order = list(samples)
                rng.shuffle(order)
                execution_order.append(dict(round=iteration, order=order))
                for arm in order:
                    if arm.startswith('prepare'):
                        results, seconds = timed(lambda: GluedCoverIndex(raw).summary, repeats[arm])
                        if any(result['component_count'] != 1 for result in results):
                            raise AssertionError('expected one torus in the odd-seam family')
                    elif arm == 'replay':
                        results, seconds = timed(lambda: verify_gauge_certificate(raw, certificate),
                                                 repeats[arm])
                        if any(result is not True for result in results):
                            raise AssertionError('gauge certificate did not replay')
                    else:
                        results, seconds = timed(lambda: index.marked_signature(0, 0, marks),
                                                 repeats[arm])
                        if any(result != expected_signature for result in results):
                            raise AssertionError('marked signature mismatch')
                    if iteration >= 0:
                        samples[arm].append(seconds)
                    del results
            medians = {arm: median(values) for arm, values in samples.items()}
            summary = index.summary
            records.append(dict(sheet_exponent=bits, sheet_bit_length=bits + 1,
                                pieces=count, seams=len(raw['seams']), marks=len(marks),
                                samples_seconds=samples, execution_order=execution_order,
                                queries_per_sample=repeats,
                                medians_seconds=medians,
                                input_bytes=len(json.dumps(json_safe(raw)).encode()),
                                summary_bytes=len(json.dumps(json_safe(summary)).encode()),
                                gauge_certificate_bytes=len(json.dumps(json_safe(certificate)).encode()),
                                signature_bytes=len(json.dumps(json_safe(expected_signature)).encode()),
                                component_count=summary['component_count'],
                                cover_degree=summary['base_components'][0]['families'][0]['cover_degree'],
                                genus=summary['base_components'][0]['families'][0]['genus']))
            print(f"W=2^{bits}, patches={count}: prep {medians['prepare']:.6f}s, "
                  f"32 marks {medians['marked']:.6f}s", flush=True)
    return records


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args(argv)
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    rng = random.Random(202610081947)
    result = dict(metadata=metadata(), scope='surface-cover geometry, not knot recognition',
                  methodology=dict(rounds=args.rounds, excluded_warmups=1,
                                   statistic='median per-query time across shuffled batches',
                                   full_preparation_in_timer=True, summary_copy_in_timer=True,
                                   input_generation_in_timer=False, serialization_in_timer=False,
                                   expanded_control='literal lifted graph and boundary permutations'),
                  expansion=expansion_benchmark(args.rounds, rng),
                  binary=binary_benchmark(args.rounds, rng))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2, sort_keys=True) + '\n')
    print(f'Wrote {args.output}', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
