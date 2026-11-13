"""Reproduce sizes and finite agreement on the supplied substantial proofs."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

from translate import backward, forward

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    tree = ast.parse(path.read_text())
    source = (ast.unparse(tree) + '\n').encode()
    return {
        'significant_tokens': sum(t.type not in IGNORED for t in
                                  tokenize.generate_tokens(io.StringIO(source.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(source),
        'gzip_9_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(source).hexdigest(),
    }


def execute(program, certificate, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / program))
    r = subprocess.run(command, input=json.dumps(certificate).encode(),
                       capture_output=True, timeout=30)
    return r.returncode == 0 and r.stdout == b'ACCEPT\n'


def main():
    rows = []
    for path in sorted((ROOT / 'fixtures').glob('*.json')):
        source = json.loads(path.read_text())
        converted = forward(source)
        assert backward(converted) == source
        expected = not path.name.startswith('future_witness')
        for optimized in (False, True):
            old = execute('control.py', source, optimized)
            new = execute('checker.py', converted, optimized)
            assert old == new == expected, (path.name, optimized, old, new)
            rows.append({'fixture': path.name, 'optimized': optimized,
                         'kind': 'inherited', 'accepted': new,
                         'inverse_translation_exact': True})
            if expected:
                corrupted = converted[:-1] + [list(converted[-1])]
                corrupted[-1][0] = [0, [0]]
                assert not execute('checker.py', corrupted, optimized)
                rows.append({'fixture': path.name, 'optimized': optimized,
                             'kind': 'false-public-conclusion', 'accepted': False})
    # Arity is checked by Python's ordinary argument binding, including at
    # the newly combined root. Every mutation keeps a false public goal.
    for tail in [[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0],
                 [0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]:
        cert = [[[0, [0]], 0] + tail]
        assert not execute('checker.py', cert, False)
        rows.append({'kind': 'false-root-arity', 'tail_length': len(tail),
                     'accepted': False})
    report = {'python': sys.version, 'metrics': {n: measure(ROOT / n)
              for n in ('control.py', 'checker.py')}, 'cases': rows,
              'all_expectations_met': True,
              'qualification': 'Finite tests support the written simulation proof; they do not prove the iPRA bridge.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'metrics': report['metrics'], 'checked_cases': len(rows),
                      'all_expectations_met': True}, indent=2))


if __name__ == '__main__':
    main()
