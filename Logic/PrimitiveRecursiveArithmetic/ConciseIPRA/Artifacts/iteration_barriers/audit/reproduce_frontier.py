"""Measure and exercise the pinned incumbent compact checkers.

This is regression evidence, not a proof of the inherited metatheorems.
"""
import ast
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'baseline' / 'shared_leaf'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def measure(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    return {'path': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(normalized.decode()).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
            'normalized_bytes': len(normalized), 'gzip9_bytes': len(compressed),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()}

def run(program, payload, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(program))
    try:
        result = subprocess.run(command, input=payload, capture_output=True, timeout=30)
        return result.returncode == 0 and result.stdout == b'ACCEPT\n'
    except subprocess.TimeoutExpired:
        return 'timeout'

def main():
    measurements = [measure(BASE / 'code' / ('checker_' + group + '.py'))
                    for group in ('tokens', 'ast', 'bytes')]
    results = []
    for group in ('tokens', 'ast', 'bytes'):
        program = BASE / 'code' / ('checker_' + group + '.py')
        for path in sorted((BASE / 'fixtures' / group).glob('*')):
            expected = not (path.name.startswith(('reject_', 'future_witness'))
                            or path.name == 'direct_false_zero_initializer.jsonl')
            payloads = [('original', path.read_bytes(), expected)]
            if expected:
                if group == 'bytes':
                    data = json.loads(path.read_text())
                    data[-1] = [[0, [0]], 0]
                    changed = json.dumps(data).encode()
                else:
                    changed = ('[0,[0]]\n' + '\n'.join(path.read_text().splitlines()[1:]) + '\n').encode()
                payloads.append(('false-public-goal', changed, False))
            for kind, payload, wanted in payloads:
                for optimized in (False, True):
                    accepted = run(program, payload, optimized)
                    results.append({'program': group, 'fixture': path.name,
                                    'kind': kind, 'optimized': optimized,
                                    'expected': wanted, 'accepted': accepted,
                                    'passed': accepted == wanted})
    report = {'repository': 'VladimirReshetnikov/ProveIt',
              'commit': '1156099ffe30f7497d2c11ab20271f46cffcd115',
              'python': platform.python_version(),
              'scope': 'Incumbent measurement and finite regression evidence only.',
              'measurements': measurements, 'executions': len(results),
              'failed_expectations': [r for r in results if not r['passed']],
              'results': results}
    (ROOT / 'audit' / 'frontier_receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['failed_expectations']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
