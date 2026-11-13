"""Focused complete-input validation and inherited theorem regressions."""
import ast
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from verify import measure


ROOT = Path(__file__).resolve().parent


def execute(job):
    case, optimized = job
    data = (json.dumps(case['input'], separators=(',', ':')) + '\n').encode()
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / 'checker_validated.py'))
    timeout = False
    try:
        result = subprocess.run(command, input=data, capture_output=True, timeout=12)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    except subprocess.TimeoutExpired:
        accepted, timeout = False, True
    return {'case': case['name'], 'kind': case['kind'],
            'optimized': optimized, 'expected': case['expected'],
            'accepted': accepted, 'timed_out': timeout,
            'passed': accepted == case['expected'] and not timeout,
            'input_sha256': hashlib.sha256(data).hexdigest()}


def main():
    compact = ast.parse((ROOT / 'compact468.py').read_text())
    validated = ast.parse((ROOT / 'checker_validated.py').read_text())
    def kernel(tree):
        return next(node for node in tree.body if isinstance(node, ast.Assign)
                    and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                    and node.targets[0].id == 'c')
    kernel_identical = ast.dump(kernel(compact)) == ast.dump(kernel(validated))
    cases = json.loads((ROOT / 'validated_fixtures.json').read_text())
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        outcomes = list(pool.map(execute, [(case, optimized) for case in cases
                                          for optimized in (False, True)]))
    failures = [row for row in outcomes if not row['passed']]
    receipt = {'python': sys.version,
               'kernel_ast_identical_to_compact468': kernel_identical,
               'metric': measure('checker_validated.py'),
               'case_count': len(cases), 'process_executions': len(outcomes),
               'positive_cases': sum(case['expected'] for case in cases),
               'negative_cases': sum(not case['expected'] for case in cases),
               'failures': failures, 'outcomes': outcomes,
               'interpretation': 'Standalone validator plus exactly the measured shifted kernel. No size record is claimed.'}
    (ROOT / 'validated_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in (
        'kernel_ast_identical_to_compact468', 'metric', 'case_count',
        'process_executions', 'positive_cases', 'negative_cases', 'failures')}, indent=2))
    if failures or not kernel_identical:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
