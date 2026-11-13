"""Reproduce a known sort-parity failure in the current computation-leaf codec.

The mutant is deliberately UNSOUND and is included only as negative evidence.
Run with CPython 3.12.14 to reproduce exact corpus metrics. No network is used.
"""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
CONTROL = ROOT / 'control_checker473.py'
MUTANT = ROOT / 'REJECTED_UNSOUND_no_parity.py'
FIXTURE = ROOT / 'false_guarded_goal.json'
IGNORE = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
          tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}


def normalized(source):
    return ast.unparse(ast.parse(source)) + '\n'


def measure(path):
    raw = path.read_bytes()
    text = normalized(raw)
    return {
        'file': path.name,
        'tokens': sum(t.type not in IGNORE
                      for t in tokenize.generate_tokens(io.StringIO(text).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(text))),
        'normalized_bytes': len(text.encode('utf-8')),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(text.encode()).hexdigest(),
    }


def integer_list_tree(value):
    return type(value) is int or (
        type(value) is list and all(integer_list_tree(v) for v in value))


def main():
    source = CONTROL.read_text()
    old = 'd % 2 * i(t, d=3)'
    if source.count(old) != 1:
        raise ValueError('The original must contain exactly one tested safeguard.')
    expected_mutant = source.replace(old, 'i(t, d=3)')
    if normalized(expected_mutant) != normalized(MUTANT.read_text()):
        raise ValueError('The mutant has changes beyond the stated deletion.')
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    if hashlib.sha256(CONTROL.read_bytes()).hexdigest() != provenance['control_source_sha256']:
        raise ValueError('Original source identity differs from the pinned copy.')

    raw = FIXTURE.read_bytes()
    certificate = json.loads(raw)
    e = [[5, 0, 0], [5, 0, [0]]]
    a = [e]
    b = [a, a, a]
    expected = [[[], 0, [], 0], [[a], 0, 0, 0],
                [[], e, a, a], [[b, a], b, a, 0], [a, 0]]
    if certificate != expected or not integer_list_tree(certificate):
        raise ValueError('The exact integer/list counterexample has changed.')

    results = []
    for program, expected_acceptance in ((CONTROL, False), (MUTANT, True)):
        for optimized in (False, True):
            command = [sys.executable, '-I', '-S', '-B']
            if optimized:
                command.append('-O')
            command.append(str(program))
            run = subprocess.run(command, input=raw, capture_output=True, timeout=10)
            accepted = run.returncode == 0 and run.stdout == b'ACCEPT\n'
            results.append({
                'program': program.name,
                'optimized': optimized,
                'expected_acceptance': expected_acceptance,
                'accepted': accepted,
                'return_code': run.returncode,
                'stdout': run.stdout.decode('utf-8', errors='replace'),
                'error_last_line': run.stderr.decode('utf-8', errors='replace').splitlines()[-1:]
            })
            if accepted != expected_acceptance:
                raise RuntimeError('Unexpected verdict: ' + repr(results[-1]))

    # The displayed formula is independent of x. At y=0 both iterators
    # give 0; at y=1 the left gives 0 and the right gives S(0)=1.
    receipt = {
        'status': 'PASS: original rejects, deliberately unsound mutant accepts',
        'python': platform.python_version(),
        'metrics': [measure(CONTROL), measure(MUTANT)],
        'fixture_sha256': hashlib.sha256(raw).hexdigest(),
        'exact_integer_list_input': True,
        'canonical_closed_guarded_goal': True,
        'false_goal_witness': {'y_zero': [0, 0], 'y_one': [0, 1],
                              'x_does_not_occur': True},
        'runs': results,
        'scope': 'Four exact process executions plus the explicit standard-model calculation; no universal correctness claim for the original from these tests.'
    }
    (ROOT / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
