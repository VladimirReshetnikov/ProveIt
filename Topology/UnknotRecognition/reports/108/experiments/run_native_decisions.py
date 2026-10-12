"""Replay exact activation-forest decisions on saved source matrices."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--solver-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--max-work', type=int, default=2000000)
    parser.add_argument('--strategy', choices=('ordered', 'output'), default='ordered')
    args = parser.parse_args()
    sys.path.insert(0, str(args.solver_dir))
    from activation_forests import solve, verify_result, parameters
    if args.strategy == 'output':
        from activation_forests import solve_output as solve, verify_output as verify_result
    source = json.loads(args.source.read_text())
    records = []
    for number, case in enumerate(source['cases']):
        item = {'id': case.get('id', f"relabel/{case['trial']}" if 'trial' in case else str(number)),
                'family': case.get('family', 'relabelled_loop_torus')}
        candidates = [('finite_boundary', case['finite_boundary']['problem'])] \
            if 'finite_boundary' in case else [('finite_boundary', case['problem'])]
        for kind, problem in candidates:
            start = time.perf_counter()
            result = solve(problem, max_work=args.max_work)
            construction = time.perf_counter() - start
            verified = None
            replay = None
            if result['status'] != 'INCONCLUSIVE':
                start = time.perf_counter()
                verified = verify_result(problem, result)
                replay = time.perf_counter()-start
                assert verified, (item['id'], result)
                expected = (case[kind]['stopping_result']['status'] == 'SUCCESS') \
                    if kind in case else case['oracle']['exists']
                assert expected == (result['status'] == 'SUCCESS'), item['id']
            item[kind] = {'parameters': parameters(problem), 'result': result,
                          'verified': verified, 'construction_seconds': construction,
                          'replay_seconds': replay}
        records.append(item)
        if number % 16 == 0 or result['status'] == 'INCONCLUSIVE':
            print(json.dumps({'index': number, 'id': item['id'],
                              'status': result['status'], 'seconds': construction}), flush=True)
    families = sorted({r['family'] for r in records})
    summary = {}
    for family in families:
        chosen = [r['finite_boundary'] for r in records if r['family'] == family]
        summary[family] = {'cases': len(chosen),
            'statuses': dict(Counter(r['result']['status'] for r in chosen)),
            'raw_k': dict(Counter(r['parameters']['raw_exceptional_columns'] for r in chosen)),
            'residual_k': dict(Counter(r['parameters']['exceptional_columns'] for r in chosen)),
            'verified': sum(r['verified'] is True for r in chosen),
            'raw_parity': sum(r['parameters']['raw_parity'] for r in chosen)}
    args.output.write_text(json.dumps({'source_file': args.source.name,
        'strategy': args.strategy, 'max_work': args.max_work,
        'summary': summary, 'cases': records}, indent=2)+'\n')
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
