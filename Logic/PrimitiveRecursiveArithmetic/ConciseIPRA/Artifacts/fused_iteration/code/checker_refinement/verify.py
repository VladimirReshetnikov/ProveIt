"""Measure full modules and compare their retained local-scope examples."""
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize
from pathlib import Path
R = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def metric(name):
    raw = (R / name).read_bytes()
    s = ast.unparse(ast.parse(raw)) + '\n'
    return {'file': name,
            'tokens': sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(s).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(s)))),
            'normalized_bytes': len(s.encode()),
            'sha256': hashlib.sha256(raw).hexdigest()}

def main():
    old = ast.parse('(k := k - 1) and (s or len(a) == 2) and k', mode='eval').body
    new = ast.parse('(k := k - 1) * (1 if s else len(a) == 2)', mode='eval').body
    class Rewrite(ast.NodeTransformer):
        count = 0
        def visit_BoolOp(self, node):
            if ast.dump(node) == ast.dump(old):
                self.count += 1
                return new
            return self.generic_visit(node)
    rewrite = Rewrite()
    transformed = rewrite.visit(ast.parse((R / 'control.py').read_text()))
    assert rewrite.count == 1
    assert ast.dump(transformed) == ast.dump(ast.parse((R / 'checker.py').read_text()))
    measurements = [metric(n) for n in ['control.py', 'checker.py']]
    assert [[m[k] for k in ('tokens', 'ast_nodes', 'normalized_bytes')]
            for m in measurements] == [[249, 267, 606], [249, 265, 605]]
    results = []
    for case in json.loads((R / 'tests/cases.json').read_text()):
        for name in ['control.py', 'checker.py']:
            for optimized in [False, True]:
                cmd = [sys.executable, '-I', '-S', '-B']
                if optimized:
                    cmd.append('-O')
                payload = (R / 'tests' / case['file']).read_bytes()
                p = subprocess.run(cmd + [str(R / name)], input=payload,
                                   capture_output=True, timeout=30)
                accepted = p.returncode == 0 and p.stdout == b'ACCEPT\n'
                results.append({'program': name, 'fixture': case['file'],
                                'optimized': optimized,
                                'accepted': accepted,
                                'expected': case['expected'],
                                'passed': accepted == case['expected'],
                                'fixture_sha256': hashlib.sha256(payload).hexdigest()})
    report = {'python': sys.version, 'measurements': measurements,
              'exact_ast_rewrite': True,
              'executions': len(results),
              'failed_expectations': sum(not r['passed'] for r in results),
              'scope': 'Finite checks supplement the universal written simulation.',
              'results': results}
    (R / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['failed_expectations']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
