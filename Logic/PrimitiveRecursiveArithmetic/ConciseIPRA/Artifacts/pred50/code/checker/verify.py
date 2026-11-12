"""Measure and compare a single, scope-preserving checker rewrite.

This is validation support, not a trusted part of either acceptance module.
The two modules have identical JSON-per-line framing. The fixture converter
recorded in provenance.json changes upstream reverse-stack files into that
framing; it does not change any packet or goal tree.
"""
import ast
import concurrent.futures
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(name):
    raw = (ROOT / name).read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    return {'path': name,
            'significant_tokens': sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'normalized_bytes': len(normalized),
            'sha256': hashlib.sha256(raw).hexdigest()}


def structural_check():
    before = (ROOT / 'control608.py').read_text()
    old = 'c(s, *g) or s * 3 if s else (a := i(*a, t, 2))'
    new = 's and c(s, *g) or s * 3 or (a := i(*a, t, 2))'
    assert before.count(old) == 1
    expected = ast.parse(before.replace(old, new))
    actual = ast.parse((ROOT / 'checker607.py').read_text())
    assert ast.dump(expected) == ast.dump(actual)
    return {'exact_single_rewrite': True,
            'scope_operations_unchanged': True,
            'stream_reader_unchanged': True,
            'public_entry_and_success_marker_unchanged': True}


def execute(task):
    file, optimized = task
    outcomes = []
    for module in ['control608.py', 'checker607.py']:
        command = [sys.executable, '-I', '-S', '-B']
        if optimized:
            command.append('-O')
        command.append(str(ROOT / module))
        proc = subprocess.run(command, input=file.read_bytes(),
                              capture_output=True, timeout=20)
        outcomes.append({'module': module,
                         'accepted': proc.returncode == 0 and proc.stdout == b'ACCEPT\n'})
    return {'fixture': file.name, 'optimized': optimized,
            'fixture_sha256': hashlib.sha256(file.read_bytes()).hexdigest(),
            'outcomes': outcomes,
            'matched': outcomes[0]['accepted'] == outcomes[1]['accepted']}


def main():
    fixtures = sorted((ROOT / 'fixtures').glob('*.jsonl'))
    tasks = [(p, optimized) for p in fixtures for optimized in [False, True]]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(execute, tasks))
    report = {'python': platform.python_version(),
              'metric': 'Complete module, ast.unparse plus final LF',
              'measurements': [measure('control608.py'), measure('checker607.py')],
              'structural_audit': structural_check(),
              'distinct_fixtures': len(fixtures),
              'executions': 2 * len(tasks),
              'disagreements': sum(not r['matched'] for r in results),
              'results': results}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['disagreements']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
