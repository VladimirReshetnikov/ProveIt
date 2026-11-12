"""Measure the complete suspended-unit experiment and check its frozen fixtures."""
import ast
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def measurements(path):
    source = path.read_bytes()
    tree = ast.parse(source)
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
               tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
    tokens = tokenize.tokenize(io.BytesIO(normalized).readline)
    return {'normalized_bytes': len(normalized),
            'significant_tokens': sum(t.type not in ignored for t in tokens),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(source).hexdigest()}


def main():
    path = ROOT / 'suspended_unit.py'
    spec = importlib.util.spec_from_file_location('suspended_unit', path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    fixtures = sorted((ROOT / 'fixtures').glob('*.json'))
    if len(fixtures) != 83:
        raise ValueError('Expected exactly 83 frozen UNIT fixtures')
    checked = []
    for fixture in fixtures:
        if checker.verify(json.loads(fixture.read_text())) is not True:
            raise ValueError('Fixture failed: ' + fixture.name)
        checked.append(fixture.name)
    report = {'python': sys.version,
              'programs': {name: measurements(ROOT / name)
                           for name in ['suspended_unit.py', 'control_step.py']},
              'in_process_positive_fixtures': len(checked),
              'fixture_names': checked,
              'status': 'All 83 frozen suspended-unit fixtures passed',
              'scope': 'Negative size experiment; no new proof-assistant verification.'}
    (ROOT / 'metrics_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
