"""Reproduce byte-profile validation and two meaningful loop regressions.

All checkers are separate subprocesses. The mutable-context mutant exists
only in a temporary directory and is never offered as a theorem checker.
"""
from pathlib import Path
import argparse
import ast
import concurrent.futures
import json
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'drafts_extracted/ipra_flat_computation_2026-11-10/ipra_flat_computation_2026-11-10'


def context_mutant(source):
    class Mutable(ast.NodeTransformer):
        def visit_AugAssign(self, node):
            self.generic_visit(node)
            if isinstance(node.target, ast.Name) and node.target.id == 'g':
                if isinstance(node.value, ast.Tuple):
                    node.value = ast.List(elts=node.value.elts, ctx=ast.Load())
            return node

        def visit_Call(self, node):
            self.generic_visit(node)
            if (isinstance(node.func, ast.Name) and node.func.id == 'c'
                    and len(node.args) == 2
                    and isinstance(node.args[1], ast.Tuple)
                    and not node.args[1].elts):
                node.args[1] = ast.List(elts=[], ctx=ast.Load())
            return node
    return ast.unparse(ast.fix_missing_locations(Mutable().visit(ast.parse(source)))) + '\n'


def run(job):
    checker, optimized, name, packet, expected, expected_recursion_error = job
    harness = "import runpy,sys;sys.setrecursionlimit(1000);runpy.run_path(sys.argv[1],run_name='__main__')"
    process = subprocess.run(
        [sys.executable, *(['-O'] if optimized else []), '-c', harness, str(checker)],
        input=json.dumps(packet), text=True, capture_output=True, timeout=30)
    accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
    rejected = process.returncode != 0 and process.stdout == 'REJECT\n'
    recursion_error = 'RecursionError' in process.stderr
    return {
        'checker': checker.name, 'optimized': optimized, 'name': name,
        'expected_accept': expected, 'accepted': accepted,
        'exit_code': process.returncode, 'protocol_valid': accepted or rejected,
        'recursion_error': recursion_error,
        'passed': accepted == expected and (accepted or rejected)
                  and (expected_recursion_error is None
                       or recursion_error == expected_recursion_error),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--loop', type=Path, default=HERE / 'loop_tuple_try.py')
    parser.add_argument('--bytes', type=Path, default=HERE / 'checker_bytes_652.py')
    parser.add_argument('--readable', type=Path, default=HERE / 'readable_loop.py')
    parser.add_argument('--baseline', type=Path, default=BASE / 'code/checker.py')
    parser.add_argument('--cases', type=Path, default=BASE / 'tests/cases.json')
    parser.add_argument('--output', type=Path, default=HERE / 'new_validation_reproduced.json')
    args = parser.parse_args()
    cases = json.loads(args.cases.read_text())['cases']
    false = [0, [0]]
    vacuous_major = [0, 0, false]
    isolation = [[[], 0, 0, 0], [vacuous_major, 0, 0, []], false]
    final = [None, 0, [0], 0]
    neutral = [None, 0, 0, 0]
    goal = [[0, [0], 0], [0]]
    deep = [final] + [neutral for _ in range(1600)] + [goal]
    jobs = [(args.bytes, opt, case['name'], case['packet'], case['accept'], None)
            for opt in (False, True) for case in cases]
    for opt in (False, True):
        for path in (args.loop, args.readable, args.baseline, args.bytes):
            jobs.append((path, opt, 'context_isolation', isolation, False, False))
            is_loop = path in (args.loop, args.readable)
            jobs.append((path, opt, 'deep_1600_continuations', deep, is_loop, not is_loop))
    with tempfile.TemporaryDirectory(prefix='ipra-invalid-control-') as tmp:
        mutant = Path(tmp) / 'mutable_context_control.py'
        mutant.write_text(context_mutant(args.loop.read_text()))
        jobs.extend((mutant, opt, 'context_isolation_mutant_control', isolation, True, False)
                    for opt in (False, True))
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            runs = list(pool.map(run, jobs))
    result = {'inherited_cases': len(cases), 'candidate_runs': 2 * len(cases),
              'new_regression_runs': len(runs) - 2 * len(cases),
              'recursion_limit': 1000, 'all_passed': all(r['passed'] for r in runs),
              'runs': runs}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'runs'}, indent=2))
    if not result['all_passed']:
        raise SystemExit(json.dumps([r for r in runs if not r['passed']], indent=2))


if __name__ == '__main__':
    main()
