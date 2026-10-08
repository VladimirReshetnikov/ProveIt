"""Paired timings of the source-braid structural specialization.

Two experiments are deliberately separate:
  encoding: run certificate versus word expansion + PD construction + Seifert;
  pipeline: recognize on fresh prebuilt diagrams, changing only braid_profile.
An identical baseline arm supplies an interleaved A/A timing control. Every
round randomizes the three arms. Validation is outside the timed batches.
Morton's 11-crossing input is a structural-only inconclusive control; its
full recognition is not timed. These selected structural families do not
establish a speedup for the general recognition pipeline.
"""
from __future__ import annotations

import argparse
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter

_root = Path(__file__).resolve().parents[1]
_fast = _root / 'fast'
if (_fast / 'fastunknot').is_dir():
    sys.path.insert(0, str(_fast))

from fastunknot.braid_profile import structural_runs_certificate
from fastunknot.diagram import Diagram
from fastunknot.recognize import recognize
from fastunknot.seifert import seifert_certificate, seifert_data


FIELDS = ('crossings', 'writhe', 'seifert_circles', 'positive_components',
          'negative_components', 'homogeneity_defect', 'canonical_genus',
          'rasmussen_interval')
MORTON = ((3, -2), (2, 1), (3, -1), (2, 1),
          (1, 3), (2, -1), (1, 1), (2, -1))


def expand(runs):
    return [index if power > 0 else -index
            for index, power in runs for _ in range(abs(power))]


def metadata(value):
    return {key: value[key] for key in FIELDS}


def experiment(rng, arms, prepare, invoke, validate, rounds, batches):
    """Prepare inputs before each timer, invoke fresh work, then validate."""
    latest = {}
    for arm in arms:
        result = invoke(arm, prepare(arm))
        validate(arm, result)
        latest[arm] = result
    samples = []
    for round_index in range(rounds):
        order = list(arms)
        rng.shuffle(order)
        sample = {'round': round_index, 'order': order, 'arms': {}}
        for arm in order:
            gc.collect()
            inputs = [prepare(arm) for _ in range(batches[arm])]
            started = perf_counter()
            results = [invoke(arm, item) for item in inputs]
            elapsed = perf_counter() - started
            for result in results:
                validate(arm, result)
            latest[arm] = results[-1]
            sample['arms'][arm] = {
                'batch': batches[arm], 'elapsed_seconds': elapsed,
                'seconds_per_call': elapsed / batches[arm],
            }
            del inputs, results
        samples.append(sample)
    medians = {arm: statistics.median(
        sample['arms'][arm]['seconds_per_call'] for sample in samples)
        for arm in arms}
    original, control, candidate = arms
    return {
        'arms': list(arms), 'samples': samples, 'median_seconds': medians,
        'median_paired_original_over_candidate': statistics.median(
            sample['arms'][original]['seconds_per_call'] /
            sample['arms'][candidate]['seconds_per_call'] for sample in samples),
        'median_paired_aa': statistics.median(
            sample['arms'][original]['seconds_per_call'] /
            sample['arms'][control]['seconds_per_call'] for sample in samples),
    }, latest


def benchmark_case(name, runs, m, rng, rounds):
    expected_profile = structural_runs_certificate(4, runs)
    expected_data = seifert_data(Diagram.from_braid(4, expand(runs)))
    assert metadata(expected_profile) == expected_data
    expected_status = expected_profile['status']
    n = expected_data['crossings']
    # The retained pilot used shorter batches and exhibited substantial A/A
    # noise on the smallest case. These fixed size-based batches make cheap
    # arms long enough for a more informative comparison; no timing result
    # is used to select an arm, case, or individual sample.
    pd_batch = max(2, min(256, 16384 // n))
    pipeline_batch = max(2, 32768 // n)
    encoding_arms = ('expanded_pd', 'expanded_pd_control', 'run_certificate')

    def invoke_encoding(arm, unused):
        if arm == 'run_certificate':
            return structural_runs_certificate(4, runs)
        # Both expansion and Diagram validation/construction are timed.
        return seifert_certificate(Diagram.from_braid(4, expand(runs)))

    def validate_encoding(arm, result):
        if result is None:
            assert expected_status == 'INCONCLUSIVE'
        else:
            assert result['status'] == expected_status
            assert result['criterion'] == expected_profile['criterion']
            assert metadata(result) == expected_data

    encoding, encoding_latest = experiment(
        rng, encoding_arms, lambda arm: None, invoke_encoding, validate_encoding,
        rounds, {'expanded_pd': pd_batch, 'expanded_pd_control': pd_batch,
                 'run_certificate': 4096})
    encoding.update({
        'timed_scope': 'RLE certificate versus expansion + PD construction + Seifert certificate',
        'parsing_timed': False,
        'all_decisions_identical': True,
        'metadata_compared_to_independent_pd_summary': True,
        'run_result': encoding_latest['run_certificate'],
        'expanded_pd_result': encoding_latest['expanded_pd'],
    })

    pipeline = None
    if m is not None:
        assert m % 2 == 1 and expected_status == 'KNOTTED'
        assert expected_profile['artin_exponent_sum'] == 1
        assert expected_profile['homogeneity_defect'] == 0
        assert expected_profile['artin_rasmussen_interval'] == [0, 0]
        pipeline_arms = ('profile_off', 'profile_off_control', 'profile_on')

        def prepare_pipeline(arm):
            diagram = Diagram.from_braid(4, expand(runs))
            assert all(key not in diagram.__dict__
                       for key in ('_alpha', '_traversal', '_faces'))
            return diagram

        def invoke_pipeline(arm, diagram):
            return recognize(diagram, use_braid_profile=(arm == 'profile_on'))

        def validate_pipeline(arm, result):
            assert result.status == expected_status
            assert result.input_crossings == n
            key = ('source_braid_structural' if arm == 'profile_on'
                   else 'seifert_certificate')
            assert metadata(result.evidence[key]) == expected_data
            assert result.evidence['braid']['status'] == 'INCONCLUSIVE'

        pipeline, pipeline_latest = experiment(
            rng, pipeline_arms, prepare_pipeline, invoke_pipeline,
            validate_pipeline, rounds, {arm: pipeline_batch for arm in pipeline_arms})
        pipeline.update({
            'timed_scope': 'recognize on fresh prebuilt Diagram objects',
            'constructor_timed': False,
            'recognize_options': {'only_changed_argument': 'use_braid_profile',
                                  'other_arguments': 'defaults'},
            'all_decisions_identical': True, 'all_structural_metadata_identical': True,
            'methods': {arm: result.method for arm, result in pipeline_latest.items()},
            'status': expected_status,
        })
    return {
        'name': name, 'm': m, 'strands': 4, 'runs': runs,
        'crossings': n, 'structural_metadata': expected_data,
        'structural_status': expected_status,
        'encoding': encoding, 'pipeline': pipeline,
        'control_note': (None if m is not None else
                         'Morton input: structural-only INCONCLUSIVE control; full recognition not timed'),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=_root / 'results' / 'benchmark_braid_profile.json')
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--m', type=int, action='append', dest='sizes',
                        help='override default odd parameters 17,129,1025,4097')
    args = parser.parse_args()
    sizes = args.sizes or [17, 129, 1025, 4097]
    if args.rounds < 1 or any(m < 3 or m % 2 == 0 for m in sizes):
        parser.error('rounds must be positive and m must be odd and at least 3')
    seed = 2026100803
    rng = random.Random(seed)
    cases = [(f'homogeneous_balanced_{m}', ((1, m), (2, -(2*m-1)), (3, m)), m)
             for m in sizes]
    cases.append(('morton_11_inconclusive', MORTON, None))
    reviewed_source = _fast / 'fastunknot' / 'braid_profile.py'
    source_hash = hashlib.sha256(reviewed_source.read_bytes()).hexdigest()
    output = {
        'schema': 'braid-profile-paired-benchmark-v1',
        'repository_parent_commit': '8126705bcb003b1082f117c87e4af7136b1d2c43',
        'braid_profile_sha256': source_hash,
        'python': platform.python_version(), 'platform': platform.platform(),
        'random_seed': seed, 'rounds': args.rounds,
        'clock': 'time.perf_counter', 'gc_enabled': gc.isenabled(),
        'design': 'randomized interleaved original, identical-original control, candidate',
        'batch_policy': {'expanded_pd': 'max(2,min(256,16384//crossings))',
                         'run_certificate': 4096,
                         'pipeline': 'max(2,32768//crossings)'},
        'interpretation': ('selected structural families only; separates encoded-input gain from '
                           'fresh-prebuilt-diagram opt-in effect; no general pipeline speedup claim'),
        'cases': [],
    }
    for name, runs, m in cases:
        row = benchmark_case(name, runs, m, rng, args.rounds)
        output['cases'].append(row)
        assert source_hash == hashlib.sha256(reviewed_source.read_bytes()).hexdigest()
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2)+'\n')
        print(name,
              'encoding ratio', round(row['encoding']['median_paired_original_over_candidate'], 3),
              'encoding A/A', round(row['encoding']['median_paired_aa'], 3),
              'pipeline ratio', None if row['pipeline'] is None else
              round(row['pipeline']['median_paired_original_over_candidate'], 3),
              'pipeline A/A', None if row['pipeline'] is None else
              round(row['pipeline']['median_paired_aa'], 3), flush=True)


if __name__ == '__main__':
    main()
