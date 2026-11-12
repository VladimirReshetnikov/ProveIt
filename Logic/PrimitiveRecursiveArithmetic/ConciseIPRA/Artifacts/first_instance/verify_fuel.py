"""Boundary and malformed-budget tests for both standalone bounded checkers."""
from pathlib import Path
import ast
import gzip
import hashlib
import importlib.util
import io
import json
import subprocess
import sys
import tokenize


HERE = Path(__file__).resolve().parent


def load(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def normalized_metrics(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
                node.body.pop(0)
    normalized = (ast.unparse(ast.fix_missing_locations(tree)) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(token.type not in ignored for token in tokenize.tokenize(io.BytesIO(normalized).readline))
    return {
        'normalized_bytes': len(normalized),
        'significant_tokens': tokens,
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'gzip_9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def accepted(module, data):
    try:
        module.check(data)
        return True
    except Exception:
        return False


def main():
    rows = []
    for filename, fixture_dir in [('checker_fuel.py', 'tests/fuel/new'),
                                  ('control_fuel.py', 'tests/fuel/old')]:
        path = HERE / 'code' / filename
        module = load(path)
        for fixture in sorted((HERE / fixture_dir).glob('*.json')):
            data = json.loads(fixture.read_text())
            large = dict(data, fuel=1000000)
            assert accepted(module, large), (filename, fixture.name, 'large budget rejected')
            used = large['fuel'] - module.fuel
            exact = dict(data, fuel=used)
            assert accepted(module, exact), (filename, fixture.name, 'exact budget rejected')
            assert module.fuel == 0
            assert not accepted(module, dict(data, fuel=used - 1)), (filename, fixture.name, 'one less accepted')
            assert not accepted(module, dict(data, fuel=0))
            for malformed in [-1, True, False, 1.0, None, '1000000', [], {}]:
                assert not accepted(module, dict(data, fuel=malformed)), (filename, malformed)
            assert not accepted(module, data)
            assert not accepted(module, dict(exact, extra=0))
            payload = json.dumps(exact)
            process = subprocess.run([sys.executable, str(path)], input=payload,
                                     text=True, capture_output=True, check=False)
            assert process.returncode == 0 and process.stdout.strip() == 'ACCEPT'
            process = subprocess.run([sys.executable, str(path)],
                                     input=json.dumps(dict(data, fuel=used - 1)),
                                     text=True, capture_output=True, check=False)
            assert process.returncode == 1 and process.stdout.strip() == 'REJECT'
            rows.append({'checker': filename, 'fixture': fixture.name,
                         'exact_fuel': used, 'exact_accepts': True,
                         'one_less_rejects': True, 'zero_rejects': True,
                         'malformed_budgets_rejected': 8,
                         'missing_and_extra_keys_rejected': True,
                         'cli_exact_and_one_less_verified': True})
    assert rows, 'No fixtures were tested.'
    report = {
        'python_version': sys.version.split()[0],
        'counter': 'One tick at every walk and derive entry; global fuel reset by every check.',
        'rows': rows,
        'metrics': {filename: normalized_metrics(HERE / 'code' / filename)
                    for filename in ['checker_fuel.py', 'control_fuel.py']},
    }
    (HERE / 'evidence' / 'fuel_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
