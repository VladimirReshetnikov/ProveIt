"""Reproduce the two independent checker comparisons and report exact sizes."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(relative):
    path = ROOT / relative
    tree = ast.parse(path.read_text())
    normalized = ast.unparse(tree) + '\n'
    return dict(path=relative, normalized_bytes=len(normalized.encode()),
                significant_tokens=sum(t.type not in SKIP for t in
                    tokenize.generate_tokens(io.StringIO(normalized).readline)),
                ast_nodes=sum(1 for _ in ast.walk(tree)),
                sha256=hashlib.sha256(path.read_bytes()).hexdigest())


for directory in ('native', 'compact'):
    completed = subprocess.run([sys.executable, str(ROOT / directory / 'reproduce.py')],
                               cwd=ROOT / directory, capture_output=True, text=True)
    if completed.returncode:
        raise RuntimeError(f'{directory} validation failed:\n{completed.stdout}\n{completed.stderr}')
    print(f'{directory}: validation passed')

native = json.loads((ROOT / 'native/validation.json').read_text())
compact = json.loads((ROOT / 'compact/evidence/results.json').read_text())
metrics = [measure(p) for p in (
    'native/control849.py', 'native/checker.py',
    'compact/reference/checker_compact_506.py', 'compact/code/checker_compact.py',
    'compact/reference/checker_guarded_exact_control.py', 'compact/code/checker_guarded_exact.py')]
expected = [(849, 370, 426), (673, 344, 393), (506, 267, 303),
            (502, 269, 301), (1176, 461, 521), (1172, 463, 519)]
for row, wanted in zip(metrics, expected):
    got = tuple(row[key] for key in ('normalized_bytes', 'significant_tokens', 'ast_nodes'))
    if got != wanted:
        raise RuntimeError(f'Unexpected normalized metric for {row["path"]}: {got}, expected {wanted}. Use CPython 3.12.14.')

summary = dict(python=sys.version, pinned_commit='6ffc49f55d355b548f7a8e1530570aee5de086b3',
               all_passed=True, metrics=metrics,
               native_fixture_processes=native['fixture_cli_processes'],
               native_total_processes=native['fixture_cli_processes'] + 1 +
                    2 * native['invalid_prefix_cases'] + 2 * native['valid_prefix_cases'] +
                    native['invalid_top_level_cases'],
               native_alphabet_comparisons=native['alphabet_comparisons'],
               compact_processes=292,
               compact_envelope_before=dict(tokens=253, ast_nodes=275, bytes=506),
               compact_envelope_after=dict(tokens=253, ast_nodes=275, bytes=502),
               new_mathematical_axiom_deletion=False,
               global_minimality_proved=False)
(ROOT / 'evidence/summary.json').write_text(json.dumps(summary, indent=2) + '\n')
(ROOT / 'evidence/summary.tex').write_text(
    '\\newcommand{\\NativeBytes}{673}\n'
    '\\newcommand{\\NativeTokens}{344}\n'
    '\\newcommand{\\NativeAST}{393}\n'
    f'\\newcommand{{\\NativeChecks}}{{{summary["native_total_processes"]}}}\n')
print(json.dumps(summary, indent=2))
