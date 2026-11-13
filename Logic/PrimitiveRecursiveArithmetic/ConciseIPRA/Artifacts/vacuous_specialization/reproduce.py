"""Reproduce the two deliberately separate checker comparisons.

Run with CPython 3.12.14 for exact normalized-source metrics. The scripts
are artifact verification tools, not dependencies of either proof checker.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def measure(relative):
    path = ROOT / relative
    raw = path.read_bytes()
    normalized = ast.unparse(ast.parse(raw)) + '\n'
    return {'file': relative,
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'normalized_bytes': len(normalized.encode('utf-8')),
            'source_sha256': hashlib.sha256(raw).hexdigest()}


def run(folder, script):
    result = subprocess.run([sys.executable, script], cwd=ROOT / folder,
                            capture_output=True, text=True, timeout=240)
    if result.returncode:
        raise RuntimeError(folder + '/' + script + '\n' + result.stdout + result.stderr)
    return {'script': folder + '/' + script, 'exit_code': result.returncode}


def main():
    runs = [run('calculus', 'test_reference.py'),
            run('calculus', 'verify_cli.py'),
            run('compact', 'verify.py')]
    paths = ['calculus/control_newest_close.py', 'calculus/checker.py',
             'compact/control474.py', 'compact/checker473.py',
             'compact/reference/control_tokens243.py',
             'compact/reference/control_ast264.py']
    metrics = [measure(p) for p in paths]
    expected = [(646, 748, 1844), (645, 745, 1830),
                (270, 308, 474), (272, 308, 473),
                (243, 271, 616), (248, 264, 613)]
    if sys.version_info[:2] == (3, 12):
        for row, triple in zip(metrics, expected):
            actual = tuple(row[k] for k in ('tokens', 'ast_nodes', 'normalized_bytes'))
            if actual != triple:
                raise RuntimeError(('unexpected metric', row, triple))
    reference = json.loads((ROOT / 'calculus/evidence.json').read_text())
    cli = json.loads((ROOT / 'calculus/cli_evidence.json').read_text())
    compact = json.loads((ROOT / 'compact/verification.json').read_text())
    result = {'python': platform.python_version(), 'runs': runs,
              'whole_module_metrics': metrics,
              'reference_checks': reference['checks'],
              'reference_passed': reference['passed'],
              'cli_checks': cli['checks'], 'cli_passed': cli['passed'],
              'compact_verification': compact,
              'all_coordinate_record_claim': False,
              'formal_proof_assistant_verification_claim': False}
    (ROOT / 'REPRODUCTION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'python': result['python'],
                      'reference': [result['reference_passed'], result['reference_checks']],
                      'cli': [result['cli_passed'], result['cli_checks']],
                      'metrics': metrics,
                      'compact': {key: compact[key] for key in
                                  ('fixture_cases', 'executions', 'failures')}}, indent=2))


if __name__ == '__main__':
    main()
