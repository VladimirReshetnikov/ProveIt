"""Recheck the late goal-directed comparison; standard library only."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
EXPECTED_CONTROL_SHA256 = 'e24664d1d6b562fe29239d6eed073ed33cae14f8b7042ddaa7c2963131161108'


def measure(path):
    tree = ast.parse(path.read_text())
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
               tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
    return {
        'normalized_bytes': len(normalized.encode()),
        'significant_tokens': sum(t.type not in ignored
                                 for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': len(list(ast.walk(tree))),
        'gzip9_bytes': len(gzip.compress(normalized.encode(), compresslevel=9, mtime=0)),
        'readable_bytes': len(path.read_bytes()),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def run(module, path, expected, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / module)]
    result = subprocess.run(command, input=path.read_bytes(), capture_output=True, timeout=30)
    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    rejected = result.returncode != 0 and result.stdout == b'REJECT\n'
    if (expected and not accepted) or (not expected and not rejected):
        raise RuntimeError(f'Unexpected result for {module}: {path.name}, optimized={optimized}')
    return {'module': module, 'fixture': str(path.relative_to(ROOT)),
            'optimized': optimized, 'expected_accept': expected, 'passed': True}


def main():
    if hashlib.sha256((ROOT / 'control_step.py').read_bytes()).hexdigest() != EXPECTED_CONTROL_SHA256:
        raise RuntimeError('The pinned upstream source has changed')
    pairs = []
    for path in sorted((ROOT / 'examples' / 'seed').glob('*.json')):
        old = ROOT / 'examples' / 'step' / path.name
        if json.loads(path.read_text())['goal'] != json.loads(old.read_text())['goal']:
            raise RuntimeError('Paired certificate goals differ: ' + path.name)
        pairs.append((path, old))
    rows = []
    for optimized in [False, True]:
        for new, old in pairs:
            for module in ['checker.py', 'checker_shared.py']:
                rows.append(run(module, new, True, optimized))
            for module in ['control_step.py', 'control_step_shared.py']:
                rows.append(run(module, old, True, optimized))
        for path in sorted((ROOT / 'examples' / 'reject').glob('*.json')):
            for module in ['checker.py', 'checker_shared.py']:
                rows.append(run(module, path, False, optimized))
    metrics = {'python': platform.python_version(),
               'control_step': measure(ROOT / 'control_step.py'),
               'initializer_evaluation': measure(ROOT / 'checker.py'),
               'shared_control_step': measure(ROOT / 'control_step_shared.py'),
               'shared_initializer_evaluation': measure(ROOT / 'checker_shared.py')}
    result = {'positive_goal_pairs': len(pairs),
              'negative_seed_cases': len(list((ROOT / 'examples' / 'reject').glob('*.json'))),
              'public_process_runs': len(rows), 'all_passed': True, 'runs': rows,
              'status': 'Finite implementation checks; not proof-assistant verification.'}
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    (ROOT / 'evidence' / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'metrics': metrics, 'positive_goal_pairs': len(pairs),
                      'negative_seed_cases': result['negative_seed_cases'],
                      'public_process_runs': len(rows), 'all_passed': True}, indent=2))


if __name__ == '__main__':
    main()
