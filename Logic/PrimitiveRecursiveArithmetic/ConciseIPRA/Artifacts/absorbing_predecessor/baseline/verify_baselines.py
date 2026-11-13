"""Remeasure frozen upstream checkers and run their retained regression cases.

No candidate checker is introduced here. Use CPython 3.12.14 for the
repository's exact normalization convention. All measured modules are
standalone and import no file from this directory.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORE = {tokenize.ENCODING, tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
          tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}


def metrics(row):
    raw = (ROOT / row['file']).read_bytes()
    normalized = ast.unparse(ast.parse(raw)) + '\n'
    values = {
        'tokens': sum(t.type not in IGNORE for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'normalized_bytes': len(normalized.encode()),
        'sha256': hashlib.sha256(raw).hexdigest(),
    }
    return {'file': row['file'], **values,
            'passed': all(row[k] == values[k] for k in values)}


def run(task):
    command = [sys.executable, '-I', '-S', '-B']
    if task['optimized']:
        command.append('-O')
    payload = (ROOT / task['fixture']).read_bytes()
    process = subprocess.run(command + [str(ROOT / task['program'])],
                             input=payload, capture_output=True, timeout=25)
    accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
    return {**task, 'accepted': accepted, 'passed': accepted == task['expected'],
            'fixture_sha256': hashlib.sha256(payload).hexdigest()}


def main():
    tasks = []
    for group, program in [('compact_context', 'compact479.py'),
                           ('native', 'native607.py'),
                           ('strict_proofs', 'strict637.py'),
                           ('strict_boundary', 'strict637.py')]:
        cases = json.loads((ROOT / 'fixtures' / group / 'cases.json').read_text())
        for case in cases:
            for optimized in (False, True):
                tasks.append({'program': 'code/' + program,
                              'fixture': 'fixtures/' + group + '/' + case['file'],
                              'expected': case['expected'], 'optimized': optimized})
    cases = json.loads((ROOT / 'stream_fixture_manifest.json').read_text())
    for case in cases:
        program = 'tokens244.py' if case['scope'] == 'global' else 'ast267.py'
        fixture = 'fixtures/stream_' + case['scope'] + '/' + Path(case['path']).name
        for optimized in (False, True):
            tasks.append({'program': 'code/' + program, 'fixture': fixture,
                          'expected': case['expected'], 'optimized': optimized})
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, tasks))
    census = json.loads((ROOT / 'frontier_census.json').read_text())
    measured = [metrics(row) for row in census['modules']]
    failures = [row for row in results + measured if not row['passed']]
    report = {'python': sys.version, 'executions': len(results),
              'metrics': measured, 'failures': failures, 'results': results,
              'scope': 'Finite regression evidence for unchanged upstream modules.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
