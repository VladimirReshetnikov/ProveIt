"""Reproduce the zero-normal companion's finite implementation evidence."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

from translate_seed import load, translate_document
from translations import fused_to_control, control_to_fused

BASE = Path(__file__).resolve().parents[1]
new = load(BASE / 'code/checker.py', 'fused_zero_kernel')
control = load(BASE / 'code/control.py', 'separate_zero_kernel')
source = load(BASE / 'reference/seed_checker.py', 'pinned_seed_kernel')


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def metrics(path):
    tree = ast.parse(path.read_text())
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    text = ast.unparse(tree) + '\n'
    skip = {tokenize.ENDMARKER, tokenize.ENCODING, tokenize.NL,
            tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {
        'normalized_bytes': len(text.encode()),
        'significant_tokens': sum(t.type not in skip for t in
                                  tokenize.generate_tokens(io.StringIO(text).readline)),
        'ast_nodes': len(list(ast.walk(tree))),
        'gzip9_bytes': len(gzip.compress(text.encode(), compresslevel=9, mtime=0)),
        'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def run():
    names = []
    for path in sorted((BASE / 'reference/seed_fixtures').glob('*.json')):
        data = json.loads(path.read_text())
        n = translate_document(data, source, new)
        c = translate_document(data, source, control, fused=False)
        c1 = {'goal': n['goal'], 'proof': fused_to_control(n['proof'], new)}
        control.check(c1)
        _, proof = control_to_fused(c['proof'], control)
        new.check({'goal': c['goal'], 'proof': proof})
        _, proof = control_to_fused(c1['proof'], control)
        new.check({'goal': n['goal'], 'proof': proof})
        require(n['goal'] == c['goal'], 'end formula changed')
        names.append(path.stem)

    cases = []
    for expectation in ['positive', 'negative']:
        for path in sorted((BASE / 'examples' / expectation).glob('*.json')):
            data = json.loads(path.read_text())
            accept = expectation == 'positive'
            try:
                new.check(data)
                actual = True
            except Exception:
                actual = False
            require(actual == accept, 'wrong in-process result: ' + path.stem)
            if accept:
                c = {'goal': data['goal'], 'proof': fused_to_control(data['proof'], new)}
                control.check(c)
                _, proof = control_to_fused(c['proof'], control)
                new.check({'goal': data['goal'], 'proof': proof})
            for optimized in [False, True]:
                command = [sys.executable] + (['-O'] if optimized else [])
                command += [str(BASE / 'code/checker.py')]
                result = subprocess.run(command, input=path.read_bytes(), capture_output=True)
                observed = result.returncode == 0 and result.stdout.strip() == b'ACCEPT'
                require(observed == accept,
                        'wrong CLI result: ' + path.stem + ' optimized=' + str(optimized))
            cases.append({'name': path.stem, 'accepted': accept})

    report = {
        'python': sys.version,
        'pinned_seed_fixtures': len(names),
        'seed_to_each_kernel': len(names),
        'fused_to_separate': len(names),
        'separate_to_fused': len(names),
        'fused_roundtrips': len(names),
        'additional_positive': sum(c['accepted'] for c in cases),
        'additional_negative': sum(not c['accepted'] for c in cases),
        'CLI_checks_normal_and_optimized': 2 * len(cases),
        'metrics': {name: metrics(BASE / 'code' / name)
                    for name in ['checker.py', 'control.py']},
        'source_cases': names,
        'additional_cases': cases,
        'limits': 'Finite implementation checks; no new proof-assistant verification.',
    }
    (BASE / 'evidence').mkdir(exist_ok=True)
    (BASE / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ['source_cases', 'additional_cases']}, indent=2))


if __name__ == '__main__':
    run()
