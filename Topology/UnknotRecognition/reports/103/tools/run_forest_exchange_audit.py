"""Retain reproducible graph-only validation and example certificates."""

import argparse
import json
from pathlib import Path
import platform
import subprocess
import sys
import time


def replay_examples(record):
    from fastunknot.core_forest_exchange_verify import verify_forest_exchange
    for example in record['examples']:
        # JSON object keys are decimal strings; source API labels are integers.
        endpoints = {int(e): ends for e, ends in example['endpoints'].items()}
        occurrences = {int(e): {int(c): value for c, value in row.items()}
                       for e, row in example['occurrences'].items()}
        if not verify_forest_exchange(example['three_handles'], endpoints, occurrences,
                                      example['result']['certificate']):
            raise RuntimeError('serialized certificate did not independently replay')
    return len(record['examples'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--replay-only', action='store_true')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(args.fast))
    evidence_path = args.output / 'forest_exchange_evidence.json'
    if args.replay_only:
        count = replay_examples(json.loads(evidence_path.read_text()))
        print(json.dumps(dict(serialized_certificates_replayed=count,
                              producer_imported=False)))
        return 0
    started = time.perf_counter()
    completed = subprocess.run(
        [sys.executable, '-m', 'unittest', 'discover', '-s', 'tests',
         '-p', 'test_core_forest_exchange.py', '-v'],
        cwd=args.fast, capture_output=True, text=True, check=False)
    elapsed = time.perf_counter() - started
    (args.output / 'forest_exchange_tests.txt').write_text(completed.stdout + completed.stderr)
    from fastunknot.core_forest_exchange import plan_forest_exchange
    from fastunknot.core_forest_exchange_verify import verify_forest_exchange
    sources = {
        'exchange_required': ([0, 1], {0: [0, 1], 1: [1], 2: [0]},
                              {0: {0: 1}, 1: {}, 2: {0: 2}}),
        'positive_deficiency': ([0], {e: [0] for e in range(5)},
                                {e: {0: 1} for e in range(5)}),
        'forced_contraction': ([0, 1], {0: [0], 1: [0, 1], 2: [1]},
                               {0: {0: 1, 1: 1, 2: 1}, 1: {1: 1}, 2: {2: 1}}),
        'strategy_limit': ([], {0: []}, {0: {0: 1, 1: 1, 2: 1}}),
    }
    examples = []
    for name, source in sources.items():
        result = plan_forest_exchange(*source)
        replayed = verify_forest_exchange(*source, result['certificate'])
        if not replayed:
            raise RuntimeError('saved example did not independently replay')
        examples.append(dict(name=name, three_handles=source[0], endpoints=source[1],
                             occurrences=source[2], result=result, independently_replayed=True))
    record = dict(scope='combinatorial graph-model validation; no native geometry benchmark',
                  python=platform.python_version(), test_exit_code=completed.returncode,
                  elapsed_seconds=elapsed, named_methods=12, exhaustive_instances=12350,
                  seeded_general_row_instances=1200, maximal_stress_bits=16385,
                  examples=examples)
    evidence_path.write_text(json.dumps(record, indent=2) + '\n')
    replay_examples(json.loads(evidence_path.read_text()))
    print(json.dumps({k: v for k, v in record.items() if k != 'examples'}, indent=2))
    return completed.returncode


if __name__ == '__main__':
    raise SystemExit(main())
