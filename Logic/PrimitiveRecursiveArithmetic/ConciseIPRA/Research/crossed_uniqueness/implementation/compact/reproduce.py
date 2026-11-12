"""Reproduce only the measured composition and its focused regression checks."""
import ast
import io
import json
import pathlib
import subprocess
import sys
import tokenize

ROOT = pathlib.Path(__file__).resolve().parent
IGNORED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
    tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def measure(path):
    normalized = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized.encode()),
    }


def accepts(program, payload, optimized=False):
    args = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / program)]
    result = subprocess.run(args, input=json.dumps(payload).encode(),
                            capture_output=True, timeout=10)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def main():
    programs = ['base506.py', 'eager503.py', 'mode505.py', 'joint502.py',
                'strict1183_control.py', 'strict1172.py']
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    measurements = {p: measure(ROOT / p) for p in programs}
    mismatches = []
    processes = 0
    for case in cases:
        payload = json.loads((ROOT / 'fixtures' / case['file']).read_text())
        for program in programs:
            strict = program.startswith('strict')
            expected = case['expected'] and (not strict or case['public_goal'])
            for optimized in (False, True):
                observed = accepts(program, payload, optimized)
                processes += 1
                if observed != expected:
                    mismatches.append([program, case['name'], optimized, expected, observed])
    valid = json.loads((ROOT / 'fixtures/computation_zero_local.json').read_text())
    for prefix in [None, True, 1.5, 'x', {}, [None]]:
        for optimized in (False, True):
            observed = accepts('strict1172.py', [prefix] + valid, optimized)
            processes += 1
            if observed:
                mismatches.append(['strict1172.py', 'invalid unused prefix', optimized, False, observed])
    old_only = json.loads((ROOT / 'fixtures/eager_control_only.json').read_text())
    certificate_difference = {p: accepts(p, old_only) for p in ['base506.py', 'eager503.py', 'joint502.py']}
    processes += 3
    result = {
        'python': sys.version,
        'metrics': measurements,
        'regression_cases': len(cases),
        'processes': processes,
        'mismatches': mismatches,
        'old_only_certificate': certificate_difference,
        'finite_tests_are_proofs': False,
    }
    (ROOT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    if mismatches:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
