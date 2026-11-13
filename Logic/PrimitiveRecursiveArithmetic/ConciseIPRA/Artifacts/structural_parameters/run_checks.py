"""Reproduce this research package. Requires only Python's standard library."""
from pathlib import Path
from hashlib import sha256
import ast
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    return {'path': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(normalized.decode()).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
            'normalized_bytes': len(normalized),
            'source_sha256': sha256(raw).hexdigest(),
            'normalized_sha256': sha256(normalized).hexdigest()}


def run_reference(data, expected, name, optimized):
    cmd = [sys.executable, '-I', '-S', '-B']
    if optimized:
        cmd.append('-O')
    cmd.append(str(ROOT / 'structural/reference_checker.py'))
    p = subprocess.run(cmd, input=data, capture_output=True, timeout=30)
    accepted = p.returncode == 0 and p.stdout == b'ACCEPT\n'
    return dict(name=name, optimized=optimized, expected=expected,
                accepted=accepted, passed=expected == accepted)


def main():
    for suite in ('structural/verify.py', 'strict/run_all.py'):
        p = subprocess.run([sys.executable, '-B', str(ROOT / suite)],
                           capture_output=True, text=True, timeout=180)
        if p.returncode:
            raise RuntimeError(suite + '\n' + p.stdout + '\n' + p.stderr)
        print(suite + ': passed')

    reference = []
    for optimized in (False, True):
        for p in sorted((ROOT / 'structural/fixtures').glob('*.jsonl')):
            reference.append(run_reference(p.read_bytes(), True, p.name, optimized))
        for p in sorted((ROOT / 'structural/negative').glob('*.jsonl')):
            reference.append(run_reference(p.read_bytes(), False, p.name, optimized))
        malformed_goals = [0, [0], [[0, 0]], [-1, -1],
                           [[0, 0, 0, 0], [0, 0, 0, 0]],
                           [3, 3], [True, True]]
        for i, a in enumerate(malformed_goals):
            data = (json.dumps(a) + '\n[0,0,0]\n').encode()
            reference.append(run_reference(data, False, 'malformed_goal_' + str(i), optimized))
        for i, a in enumerate([False, 0.0, '', {}, None]):
            data = ('[[0,0,0],0]\n' + json.dumps([a, 0, 0]) + '\n').encode()
            reference.append(run_reference(data, False, 'malformed_packet_' + str(i), optimized))

    structural = json.loads((ROOT / 'structural/verification_receipt.json').read_text())
    strict = json.loads((ROOT / 'strict/validation.json').read_text())
    files = ['structural/checker_opaque_stream.py',
             'structural/reference_checker.py',
             'structural/controls/checker_tokens239.py',
             'reference/compact_ast255.py', 'reference/compact_bytes460.py',
             'strict/checkers/strict_tokens299.py',
             'strict/checkers/strict_ast335.py',
             'strict/checkers/strict_bytes583.py']
    failures = [r for r in reference if not r['passed']]
    result = dict(python=platform.python_version(),
                  source_commit='0198424b74acc33db20c5180c8019ecd7d14a75a',
                  requested_global_target_met=False,
                  metrics=[measure(ROOT / p) for p in files],
                  structural_executions=structural['execution_count'],
                  opaque_fixed_point_checks=structural['opaque_fixed_point_checks'],
                  strict_executions=strict['executions'],
                  reference_executions=len(reference),
                  reference_results=reference,
                  failures=failures,
                  evidence_limit='Finite tests plus written proofs; no proof-assistant verification of Python execution.')
    (ROOT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    if failures:
        raise RuntimeError(json.dumps(failures, indent=2))
    print(json.dumps({k: result[k] for k in ('python', 'structural_executions',
          'opaque_fixed_point_checks', 'strict_executions', 'reference_executions', 'failures')}, indent=2))


if __name__ == '__main__':
    main()
