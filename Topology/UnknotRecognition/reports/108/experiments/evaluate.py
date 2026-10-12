"""Run the new kernel on every freshly reconstructed uncapped native matrix."""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--code', type=Path, required=True)
    parser.add_argument('--max-work', type=int, default=1000000)
    args = parser.parse_args()
    sys.path.insert(0, str(args.code.resolve()))
    from activation_forests import solve, parameters, verify_result
    from activation_forests.model import parse_problem
    source_bytes = args.input.read_bytes()
    bank = json.loads(source_bytes)
    records = []
    all_counts = Counter()
    for case in bank['cases']:
        record = {'id': case['id'], 'family': case['family'],
                  'tetrahedra': case['tetrahedra'],
                  'three_handles': case['three_handles'],
                  'native_source_sha256': sha256(json.dumps(case['native_source'],
                    sort_keys=True, separators=(',', ':')).encode()).hexdigest()}
        for label in ('source', 'finite_boundary'):
            if label not in case:
                continue
            problem = case[label]['problem']
            parsed = parse_problem(problem)
            params = parameters(problem)
            started = time.perf_counter()
            answer = solve(problem, max_work=args.max_work)
            produced = time.perf_counter() - started
            verified, checked = None, None
            if answer['status'] != 'INCONCLUSIVE':
                started = time.perf_counter()
                verified = verify_result(problem, answer)
                checked = time.perf_counter() - started
                assert verified, (case['id'], label, answer)
                previous = case[label]['stopping_result']['status']
                if previous != 'INCONCLUSIVE':
                    assert answer['status'] == previous, (case['id'], label, previous, answer)
                oracle = case[label]['tree_oracle']
                if oracle['status'] == 'COMPLETE':
                    assert (answer['status'] == 'SUCCESS') == oracle['exists']
            record[label] = {'problem_sha256': parsed.digest,
                             'parameters': params, 'answer': answer,
                             'independent_replay': verified,
                             'production_seconds': produced,
                             'verification_seconds': checked,
                             'previous_exact_status': case[label]['stopping_result']['status'],
                             'tree_oracle_status': case[label]['tree_oracle']['status']}
            all_counts[label+'/'+answer['status']] += 1
            all_counts[label+'/raw_parity'] += parsed.raw_parity
            all_counts[label+'/verified'] += bool(verified)
            print(json.dumps({'id': case['id'], 'matrix': label,
                              'status': answer['status'], 'raw_k': params['raw_exceptional_columns'],
                              'k': params['exceptional_columns'], 'raw_parity': parsed.raw_parity,
                              'work': answer['stats']['structural_work']}), flush=True)
        records.append(record)
    groups = {}
    for family in sorted({r['family'] for r in records}):
        group = [r for r in records if r['family'] == family]
        groups[family] = {'cases': len(group)}
        for label in ('source', 'finite_boundary'):
            items = [r[label] for r in group if label in r]
            groups[family][label] = {
                'statuses': dict(Counter(r['answer']['status'] for r in items)),
                'verified_complete': sum(bool(r['independent_replay']) for r in items),
                'raw_parity_cases': sum(r['parameters']['raw_parity'] for r in items),
                'raw_k': dict(Counter(str(r['parameters']['raw_exceptional_columns']) for r in items)),
                'residual_k': dict(Counter(str(r['parameters']['exceptional_columns']) for r in items)),
                'max_work': max((r['answer']['stats']['structural_work'] for r in items), default=0),
            }
    modules = args.code/'activation_forests'
    payload = {'scope': 'Source-reconstructed uncapped graph/matrix operations, each fixing the recorded primal forest. Timing fields are single validation runs, not paired performance claims.',
               'input_path': str(args.input), 'input_sha256': sha256(source_bytes).hexdigest(),
               'max_work': args.max_work,
               'code_sha256': {p.name: sha256(p.read_bytes()).hexdigest()
                               for p in sorted(modules.glob('*.py'))},
               'counts': dict(all_counts), 'families': groups, 'cases': records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps(groups, indent=2), flush=True)


if __name__ == '__main__':
    main()
