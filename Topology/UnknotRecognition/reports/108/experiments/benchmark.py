"""Paired finite-kernel timings; geometry construction is outside the timer.

Every raw trial is retained. Resource-capped outcomes are reported explicitly.
No equivalence between the two algorithms' different work units is assumed.
"""
import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--native', type=Path, required=True)
    ap.add_argument('--relabels', type=Path, required=True)
    ap.add_argument('--code', type=Path, required=True)
    ap.add_argument('--dual-code', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--repetitions', type=int, default=7)
    ap.add_argument('--max-work', type=int, default=1000000)
    ap.add_argument('--max-nodes', type=int, default=50000)
    ap.add_argument('--methods', nargs='+', default=['degree_two', 'stopping',
                    'ordered', 'ordered_no_rank', 'output', 'output_no_rank'])
    args = ap.parse_args()
    sys.path[:0] = [str(args.code), str(args.dual_code)]
    from activation_forests import solve, verify_result, parameters
    from activation_forests.output_solver import solve_output
    from activation_forests.output_verify import verify_output
    from dual_forest_search import solve_degree_two, solve_by_stopping
    from dual_forest_verify import verify as verify_old
    funcs = {
        'degree_two': (solve_degree_two, verify_old),
        'stopping': (lambda p: solve_by_stopping(p, max_nodes=args.max_nodes), verify_old),
        'ordered': (lambda p: solve(p, max_work=args.max_work), verify_result),
        'ordered_no_rank': (lambda p: solve(p, max_work=args.max_work,
                                          use_rank_layer=False), verify_result),
        'output': (lambda p: solve_output(p, max_work=args.max_work), verify_output),
        'output_no_rank': (lambda p: solve_output(p, max_work=args.max_work,
                                                use_rank_layer=False), verify_output),
    }
    cases = []
    for c in json.loads(args.native.read_text())['cases']:
        problem = c['finite_boundary']['problem']
        old = c['finite_boundary']['stopping_result']['status']
        cases.append({'id': c['id'], 'family': c['family'], 'problem': problem,
                      'expected': old if old != 'INCONCLUSIVE' else None})
    for c in json.loads(args.relabels.read_text())['cases']:
        cases.append({'id': 'relabel/'+str(c['trial']), 'family': 'relabelled_loop_torus',
                      'problem': c['problem'],
                      'expected': 'SUCCESS' if c['oracle']['exists'] else 'NO_FOREST'})
    rng = random.Random(20261012519)
    records = []
    begun = time.perf_counter()
    # Rotate the algorithm order independently within each paired repetition.
    for index, case in enumerate(cases):
        record = {k: case[k] for k in ('id', 'family', 'expected')}
        record['parameters'] = parameters(case['problem'])
        record['trials'] = {m: [] for m in args.methods}
        for rep in range(args.repetitions):
            order = list(args.methods)
            rng.shuffle(order)
            for method in order:
                run, check = funcs[method]
                start = time.perf_counter_ns()
                result = run(case['problem'])
                elapsed = (time.perf_counter_ns()-start)/1e9
                verified = None
                if result['status'] != 'INCONCLUSIVE':
                    verified = bool(check(case['problem'], result))
                    assert verified, (case['id'], method, result)
                    if case['expected'] is not None:
                        assert result['status'] == case['expected'], (case['id'], method)
                record['trials'][method].append({'repetition': rep, 'seconds': elapsed,
                    'status': result['status'], 'verified': verified,
                    'stats': result.get('stats', {})})
        records.append(record)
        if index % 32 == 0 or case['family'] in ('stellar_torus', 'nested_interior_torus'):
            print(json.dumps({'case': case['id'], 'done': index+1,
                'medians': {m: statistics.median(t['seconds'] for t in ts)
                            for m, ts in record['trials'].items()},
                'statuses': {m: ts[0]['status'] for m, ts in record['trials'].items()}}),
                  flush=True)
    summary = {}
    for family in sorted({c['family'] for c in records}):
        chosen = [c for c in records if c['family'] == family]
        summary[family] = {}
        for method in args.methods:
            medians = [statistics.median(t['seconds'] for t in c['trials'][method])
                       for c in chosen]
            summary[family][method] = {'cases': len(chosen),
                'statuses': dict(Counter(c['trials'][method][0]['status'] for c in chosen)),
                'sum_case_medians_seconds': sum(medians),
                'median_case_seconds': statistics.median(medians),
                'maximum_case_seconds': max(medians),
                'verified_complete_trials': sum(t['verified'] is True for c in chosen
                                                for t in c['trials'][method])}
    code_files = list((args.code/'activation_forests').glob('*.py')) + [
        args.dual_code/'dual_forest_search.py', args.dual_code/'dual_forest_verify.py']
    payload = {'scope': 'Paired finite-matrix kernels on identical uncapped inputs; '
        'source reconstruction, parameter reporting, and certificate replay are untimed. '
        'Every successful or negative trial replayed independently. Censored results retained.',
        'python': sys.version, 'platform': platform.platform(),
        'processor': platform.processor(), 'seed': 20261012519,
        'repetitions': args.repetitions, 'max_work': args.max_work,
        'max_nodes': args.max_nodes, 'methods': args.methods,
        'input_sha256': {p.name: sha256(p.read_bytes()).hexdigest()
                         for p in (args.native, args.relabels)},
        'code_sha256': {p.name: sha256(p.read_bytes()).hexdigest() for p in code_files},
        'elapsed_seconds': time.perf_counter()-begun, 'summary': summary, 'cases': records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
