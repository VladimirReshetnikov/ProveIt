"""Same-input interface benchmark: expanded PD vs signed-run certificates.

Each case starts from ONE already parsed immutable tuple of four runs on
five strands: [1,m], [2,-m], [3,m], [4,-m]. JSON parsing and construction of
that shared input are outside the timers. Arms A and A/A each freshly expand
the word, construct/validate Diagram.from_braid, then call seifert_certificate.
Arm B freshly calls signed_run_certificate 100 times per sample by default;
its measured batch duration is divided by the batch size. All common output
fields agree, and every B answer passes the independent signed-run verifier.
Comparison and verification are outside the timers.

This times one certificate interface, not the complete recognition portfolio
or residual hard-unknot instances. The virtual environment is uncontrolled.
"""
import argparse
import csv
import hashlib
import inspect
import json
import platform
import random
import sys
from pathlib import Path
from statistics import median
from time import perf_counter

BUNDLE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BUNDLE_ROOT / "implementation" / "fast"))

from fastunknot.diagram import Diagram
from fastunknot.seifert import seifert_certificate
from fastunknot.symbolic_braid import (
    signed_run_certificate, verify_signed_run_certificate,
)
from fastunknot.twist.core import Run


def expanded_certificate(strands, runs):
    word = [run.generator * (1 if run.exponent > 0 else -1)
            for run in runs for _ in range(abs(run.exponent))]
    diagram = Diagram.from_braid(strands, word)
    return seifert_certificate(diagram)


def source_hash(function):
    return hashlib.sha256(Path(inspect.getsourcefile(function)).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--direct-batch', type=int, default=100)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('signed_run_structural_benchmark.json'))
    parser.add_argument('--summary', type=Path,
                        default=Path(__file__).with_name('signed_run_structural_summary.csv'))
    args = parser.parse_args()
    if args.rounds < 1 or args.direct_batch < 1:
        parser.error('rounds and direct-batch must be positive')
    seed = 2026100802
    rng = random.Random(seed)
    records, summaries = [], []
    result = {
        'python': platform.python_version(), 'platform': platform.platform(),
        'seed': seed, 'rounds': args.rounds, 'direct_batch': args.direct_batch,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'diagram_sha256': source_hash(Diagram.from_braid),
        'seifert_sha256': source_hash(seifert_certificate),
        'symbolic_braid_sha256': source_hash(signed_run_certificate),
        'shared_input': 'already parsed tuple of four signed Run objects, strands=5',
        'arm_A': 'word expansion + fresh Diagram.from_braid construction/validation + seifert_certificate',
        'arm_AA': 'second independent invocation of exactly arm A',
        'arm_B': 'batch of fresh signed_run_certificate calls; batch elapsed time divided by batch size',
        'B_batch_overhead': 'loop and output-list append included in the measured batch',
        'excluded': 'JSON parsing, construction of the shared run tuple, comparison, independent verification, and serialization',
        'caveat': 'noisy shared virtual environment; certificate interface only, not full recognition portfolio or hard-unknot performance',
        'records': records,
    }
    for magnitude in (101, 1001, 10001):
        strands = 5
        runs = (Run(1, magnitude), Run(2, -magnitude),
                Run(3, magnitude), Run(4, -magnitude))
        rounds = []
        certificate = None
        verifier_calls = 0
        for round_index in range(args.rounds):
            arms = ['expanded', 'expanded_AA', 'direct_runs']
            rng.shuffle(arms)
            elapsed = {}
            outputs = {}
            for arm in arms:
                if arm == 'direct_runs':
                    batch = []
                    start = perf_counter()
                    for _ in range(args.direct_batch):
                        batch.append(signed_run_certificate(strands, runs))
                    elapsed[arm] = perf_counter() - start
                    outputs[arm] = batch
                else:
                    start = perf_counter()
                    answer = expanded_certificate(strands, runs)
                    elapsed[arm] = perf_counter() - start
                    outputs[arm] = answer
            baseline = outputs['expanded']
            if baseline is None or baseline != outputs['expanded_AA']:
                raise AssertionError('expanded A/A answers differ or fail to certify')
            for direct in outputs['direct_runs']:
                if direct is None or not baseline.keys() <= direct.keys():
                    raise AssertionError('direct certificate omits baseline fields')
                if any(direct[key] != value for key, value in baseline.items()):
                    raise AssertionError('a common certificate field disagrees')
                if not verify_signed_run_certificate(strands, runs, direct):
                    raise AssertionError('independent certificate verifier failed')
                verifier_calls += 1
            certificate = outputs['direct_runs'][-1]
            if (certificate['status'] != 'KNOTTED' or
                    certificate['criterion'] != 'homogeneous-seifert-genus' or
                    certificate['crossings'] != 4 * magnitude or
                    certificate['canonical_genus'] != 2 * magnitude - 2 or
                    certificate['writhe'] != 0 or
                    certificate['rasmussen_interval'] != [0, 0]):
                raise AssertionError('balanced family has unexpected structural data')
            per_call = elapsed['direct_runs'] / args.direct_batch
            rounds.append({
                'round': round_index, 'arm_order': arms,
                'expanded_seconds': elapsed['expanded'],
                'expanded_AA_seconds': elapsed['expanded_AA'],
                'direct_batch_seconds': elapsed['direct_runs'],
                'direct_seconds_per_call': per_call,
                'paired_speedup': elapsed['expanded'] / per_call,
                'AA_ratio': elapsed['expanded'] / elapsed['expanded_AA'],
            })
        common_fields = sorted(baseline)
        record = {
            'magnitude': magnitude, 'strands': strands,
            'runs': [[run.generator, run.exponent] for run in runs],
            'certificate': certificate, 'common_fields_compared': common_fields,
            'all_common_fields_equal': True,
            'independent_verifier_calls': verifier_calls,
            'all_independent_verifications_passed': True,
            'rounds': rounds,
            'median_expanded_seconds': median(r['expanded_seconds'] for r in rounds),
            'median_direct_batch_seconds': median(r['direct_batch_seconds'] for r in rounds),
            'median_direct_seconds_per_call': median(r['direct_seconds_per_call'] for r in rounds),
            'median_paired_speedup': median(r['paired_speedup'] for r in rounds),
            'median_AA_ratio': median(r['AA_ratio'] for r in rounds),
        }
        records.append(record)
        summaries.append({
            'magnitude': magnitude, 'expanded_crossings': 4 * magnitude,
            'canonical_genus': certificate['canonical_genus'],
            'median_expanded_seconds': record['median_expanded_seconds'],
            'direct_batch': args.direct_batch,
            'median_direct_batch_seconds': record['median_direct_batch_seconds'],
            'median_direct_seconds_per_call': record['median_direct_seconds_per_call'],
            'median_paired_speedup': record['median_paired_speedup'],
            'median_AA_ratio': record['median_AA_ratio'],
        })
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        with args.summary.open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=list(summaries[0]))
            writer.writeheader()
            writer.writerows(summaries)
        print('m=', magnitude, 'expanded=', round(record['median_expanded_seconds'], 6),
              'direct_us=', round(1e6 * record['median_direct_seconds_per_call'], 3),
              'speedup=', round(record['median_paired_speedup'], 2),
              'AA=', round(record['median_AA_ratio'], 3), flush=True)


if __name__ == '__main__':
    main()
