"""Offline structural audit and regression of the whole-input 269-node checker."""
from pathlib import Path
import ast
import copy
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def metrics(name):
    data = (ROOT / name).read_bytes()
    source = ast.unparse(ast.parse(data)) + '\n'
    return {
        'program': name,
        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
        'normalized_bytes': len(source.encode()),
        'sha256': hashlib.sha256(data).hexdigest(),
    }


def structural_check():
    old = ast.parse('(k := k - 1) and (s or len(a) == 2) and k', mode='eval').body
    new = ast.parse('(k := k - 1) * (1 if s else len(a) == 2)', mode='eval').body

    class Rewrite(ast.NodeTransformer):
        count = 0

        def visit_BoolOp(self, node):
            if ast.dump(node) == ast.dump(old):
                self.count += 1
                return copy.deepcopy(new)
            return self.generic_visit(node)

    rewrite = Rewrite()
    tree = rewrite.visit(ast.parse((ROOT / 'control271.py').read_text()))
    actual = ast.parse((ROOT / 'checker269.py').read_text())
    if rewrite.count != 1 or ast.dump(tree) != ast.dump(actual):
        raise ValueError('Candidate is not exactly the one-expression rewrite.')
    return True


def main():
    control_data = (ROOT / 'control271.py').read_bytes()
    control_blob = hashlib.sha1(b'blob ' + str(len(control_data)).encode() + b'\0' + control_data).hexdigest()
    if control_blob != '6b7b3bbba4ffc95f9d10081477096d910be1ace9':
        raise ValueError('Matched control differs from its pinned Git blob.')
    exact_rewrite = structural_check()
    sizes = [metrics(name) for name in ('control271.py', 'checker269.py')]
    if [[m[k] for k in ('tokens', 'ast_nodes', 'normalized_bytes')] for m in sizes] != [[255, 271, 606], [255, 269, 605]]:
        raise ValueError('Unexpected size profile; use CPython 3.12.14.')
    cases = json.loads((ROOT / 'fixtures' / 'manifest.json').read_text())
    results = []
    hashes = set()
    for case in cases:
        data = (ROOT / 'fixtures' / case['file']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != case['source_sha']:
            raise ValueError('Fixture differs from pinned upstream bytes: ' + case['file'])
        digest = hashlib.sha256(data).hexdigest()
        hashes.add(digest)
        for name in ('control271.py', 'checker269.py'):
            for optimized in (False, True):
                command = [sys.executable, '-I', '-S', '-B']
                if optimized:
                    command.append('-O')
                proc = subprocess.run(command + [str(ROOT / name)], input=data,
                                      capture_output=True, timeout=20)
                accepted = proc.returncode == 0 and proc.stdout == b'ACCEPT\n'
                results.append({
                    'fixture': case['file'], 'fixture_sha256': digest,
                    'program': name, 'optimized': optimized,
                    'expected': case['expected'], 'accepted': accepted,
                    'passed': accepted == case['expected'],
                })
    report = {
        'python': platform.python_version(), 'exact_one_expression_ast_rewrite': exact_rewrite,
        'control_git_blob_sha1': control_blob,
        'metrics': sizes, 'fixture_paths': len(cases), 'distinct_fixture_payloads': len(hashes),
        'cli_executions': len(results),
        'failed_expectations': sum(not r['passed'] for r in results),
        'results': results,
        'limits': [
            'Finite tests supplement a written simulation; they do not prove the calculus soundness or bi-interpretation.',
            'Inherited raw aliases are regression fixtures and are not all canonical public formulas.',
            'The comparison concerns sufficient resources and finite exact-integer/list certificate data.',
        ],
    }
    (ROOT / 'verification269.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['failed_expectations']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
