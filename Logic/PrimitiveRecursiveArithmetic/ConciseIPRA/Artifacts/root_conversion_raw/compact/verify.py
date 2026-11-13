"""Focused comparisons for the eager-mode/strict-opening composition."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
CASES = json.loads((ROOT / 'fixtures/cases.json').read_text())
PROGRAMS = ['reference/control477.py', 'checker476.py', 'readable_checker.py']
SKIP = {tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT, tokenize.NEWLINE,
        tokenize.NL, tokenize.ENDMARKER, tokenize.ENCODING}


def measure(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    data = source.encode()
    return {
        'tokens': sum(t.type not in SKIP for t in
                      tokenize.generate_tokens(io.StringIO(source).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(source)))),
        'normalized_bytes': len(data),
        'gzip9_bytes_mtime0': len(gzip.compress(data, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def run(job):
    case, program, optimized = job
    cmd = [sys.executable, '-I', '-S', '-B']
    if optimized:
        cmd.append('-O')
    cmd.append(str(ROOT / program))
    result = subprocess.run(cmd, input=(ROOT / 'fixtures' / case['file']).read_bytes(),
                            capture_output=True, timeout=10)
    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return {'fixture': case['file'], 'program': program,
            'optimized': optimized, 'accepted': accepted,
            'expected': case['candidate_expected'],
            'passed': accepted == case['candidate_expected']}


jobs = [(case, program, optimized) for case in CASES for program in PROGRAMS
        for optimized in (False, True)]
with ThreadPoolExecutor(max_workers=8) as pool:
    results = list(pool.map(run, jobs))
failures = [row for row in results if not row['passed']]
report = {'python': sys.version, 'fixtures': len(CASES), 'executions': len(results),
          'metrics': {p: measure(ROOT / p) for p in PROGRAMS},
          'failures': failures, 'results': results}
(ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({key: value for key, value in report.items() if key != 'results'}, indent=2))
if failures:
    raise SystemExit(1)
