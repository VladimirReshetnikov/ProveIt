#!/usr/bin/env python3
"""Re-run the frozen exact checks in both Python modes, standard library only."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='destination JSON (default stdout)')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    script = root / 'verify_report177.py'
    tree = ast.parse(script.read_text(encoding='utf-8'))
    require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
            'verifier contains an optimizable assertion statement')
    allowed = {'__future__', 'argparse', 'dataclasses', 'fractions', 'functools',
               'itertools', 'json', 'math', 'pathlib', 'subprocess', 'sys'}
    imports = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name.split('.')[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imports.add(node.module.split('.')[0])
    require(imports <= allowed, 'unexpected non-standard-library dependency')
    hashes = {}
    with tempfile.TemporaryDirectory(prefix='report177-reproduce-') as temporary:
        directory = Path(temporary)
        normal_bytes = None
        for mode, switches in [('normal', ['-E']), ('optimized', ['-E', '-O'])]:
            destination = directory / (mode + '.json')
            run = subprocess.run([sys.executable] + switches + [str(script), '--output', str(destination)],
                                 capture_output=True, text=True, check=False)
            require(run.returncode == 0, f'{mode} run failed: {run.stderr}')
            data = destination.read_bytes()
            require(data == (root / 'checks.json').read_bytes(), f'{mode} output differs from frozen checks.json')
            if normal_bytes is None:
                normal_bytes = data
            require(data == normal_bytes, 'normal/-O complete output differs')
            hashes[mode] = hashlib.sha256(data).hexdigest()
        extended = directory / 'order5.json'
        run = subprocess.run([sys.executable, '-E', str(script), '--order', '5', '--output', str(extended)],
                             capture_output=True, text=True, check=False)
        require(run.returncode == 0, f'order-five extension failed: {run.stderr}')
        require(extended.read_bytes() == (root / 'checks.order5.json').read_bytes(),
                'order-five output differs from frozen checks.order5.json')
        hashes['order5'] = hashlib.sha256(extended.read_bytes()).hexdigest()
        invalid = subprocess.run([sys.executable, '-E', str(script), '--order', '2'],
                                 capture_output=True, text=True, check=False)
        require(invalid.returncode != 0 and not invalid.stdout, 'invalid command-line order was accepted')
    result = {'status': 'passed', 'standard_library_imports_only': True,
              'optimizable_assertion_statement_count': 0,
              'normal_optimized_and_frozen_order3_outputs_byte_identical': True,
              'order5_extension_matches_frozen_output': True,
              'invalid_command_line_order_rejected': True, 'output_sha256': hashes}
    text = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.output is None:
        sys.stdout.write(text)
    else:
        args.output.write_text(text, encoding='utf-8')


if __name__ == '__main__':
    main()
