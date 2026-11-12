"""Reproduce source provenance, exact metrics, framing, and finite validation.

This harness and the format converter are untrusted support code. The measured
checkers are standalone modules and import only Python's standard json module.
Tests supplement the written simulation and canonical-completeness proofs.
"""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}


def normalize(source):
    return ast.unparse(ast.parse(source)) + '\n'


def measure(path):
    raw = path.read_bytes()
    source = normalize(raw)
    return dict(path=path.relative_to(ROOT).as_posix(),
                tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(source)))),
                normalized_bytes=len(source.encode()),
                sha256=hashlib.sha256(raw).hexdigest())


def json_lines(array):
    return ''.join(json.dumps(v, separators=(',', ':')) + '\n' for v in reversed(array))


def opening(a, t=None, d=0):
    if isinstance(a, list):
        return [opening(b, t, d + 5 - len(a)) for b in a]
    return a if 0 <= a < d else d % 2 and opening(t, d=3)


def numeral(n):
    a = 0
    for _ in range(n):
        a = [a]
    return a


def generated_computations():
    """Canonical closed zero/successor computation instances and corruptions."""
    rows = []
    for seed in range(1, 4):
        for h in (0, [0], 3, [7]):
            u = numeral(seed)
            goal = [[0, u, h], u]
            rows.append(([0, 0, u, h], goal))
            for n in range(1, 5):
                s = numeral(n)
                goal = [[[s], u, h], opening(h, [s, u, h], 3)]
                rows.append(([0, s, u, h], goal))
    return rows


def run(task):
    label, program, payload, optimized, expected = task
    command = [sys.executable, '-I', '-S', '-B', *(['-O'] if optimized else []),
               str(ROOT / program)]
    try:
        p = subprocess.run(command, input=payload, text=True, capture_output=True, timeout=20)
        accepted = p.returncode == 0 and p.stdout == 'ACCEPT\n'
        return dict(case=label, program=program, optimized=optimized,
                    expected=expected, accepted=accepted, passed=accepted == expected)
    except subprocess.TimeoutExpired:
        return dict(case=label, program=program, optimized=optimized,
                    expected=expected, passed=False, error='timeout')


def main():
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    for row in provenance['files']:
        data = (ROOT / row['local_path']).read_bytes()
        sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if sha != row['blob_sha']:
            raise ValueError('Upstream source mismatch: ' + row['local_path'])

    incoming = json.loads((ROOT / 'INCOMING_PROVENANCE.json').read_text())
    for row in incoming['members']:
        data = (ROOT / row['local_path']).read_bytes()
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('Incoming archive member mismatch: ' + row['local_path'])

    replacements = [
        ('controls/checker479.py', 'code/checker478.py',
         'bool(m or 3 % len(a))', 'any((m, 3 % len(a)))'),
        ('controls/checker637.py', 'code/checker636.py',
         'bool(m or len(a) % 2 == u)', 'any((m, len(a) % 2 == u))'),
    ]
    for old, new, before, after in replacements:
        source = (ROOT / old).read_text()
        if source.count(before) != 1:
            raise ValueError('Unexpected baseline source')
        if normalize(source.replace(before, after)) != (ROOT / new).read_text():
            raise ValueError('Candidate contains an unaudited edit')
    for old, new in [('controls/incoming_tokens244.py', 'code/checker244.py'),
                     ('controls/incoming_ast267.py', 'code/checker267.py')]:
        source = (ROOT / old).read_text().replace('from json import loads', 'from json import *')
        if normalize(source) != (ROOT / new).read_text():
            raise ValueError('Stream candidate contains an unaudited edit')

    metrics = [measure(p) for d in ['controls', 'code'] for p in sorted((ROOT / d).glob('*.py'))]
    expected_metrics = {
        'controls/tokens248.py': (248, 277, 609),
        'controls/incoming_tokens244.py': (244, 272, 608),
        'controls/incoming_ast267.py': (249, 267, 606),
        'controls/ast270.py': (254, 270, 608),
        'controls/checker479.py': (272, 304, 479),
        'controls/checker637.py': (344, 392, 637),
        'code/checker244.py': (244, 272, 604),
        'code/checker267.py': (249, 267, 602),
        'code/checker478.py': (274, 304, 478),
        'code/checker636.py': (346, 392, 636),
    }
    for row in metrics:
        if (row['tokens'], row['ast_nodes'], row['normalized_bytes']) != expected_metrics[row['path']]:
            raise ValueError('Metric differs from CPython 3.12.14 reference: ' + repr(row))

    tasks = []

    def add(label, program, payload, expected):
        for optimized in (False, True):
            tasks.append((label, program, payload, optimized, expected))

    for mode, old, new in [('global', 'incoming_tokens244.py', 'checker244.py'),
                           ('local', 'incoming_ast267.py', 'checker267.py')]:
        for folder, expected in [(mode, True), ('adversarial', False)]:
            for p in sorted((ROOT / 'fixtures/three_field' / folder).glob('*.json')):
                data = json.loads(p.read_text())
                add(p.relative_to(ROOT).as_posix(), 'controls/' + old, json_lines(data), expected)
                add(p.relative_to(ROOT).as_posix(), 'code/' + new, json_lines(data), expected)

    for family, folders, programs in [
        ('byte', ['context', 'progress'], ['controls/checker479.py', 'code/checker478.py']),
        ('native', ['proofs', 'boundary'], ['controls/checker637.py', 'code/checker636.py']),
    ]:
        for folder in folders:
            directory = ROOT / 'fixtures' / family / folder
            for row in json.loads((directory / 'cases.json').read_text()):
                p = directory / row['file']
                for program in programs:
                    add(p.relative_to(ROOT).as_posix(), program, p.read_text(), row['expected'])

    generated = generated_computations()
    for n, (packet, goal) in enumerate(generated):
        for expected in (True, False):
            tested_goal = goal if expected else [goal[0], numeral(12)]
            four = [packet, tested_goal]
            three = [packet[1:], tested_goal]
            label = 'generated/' + str(n) + ('/valid' if expected else '/wrong_endpoint')
            for program in ['controls/checker479.py', 'code/checker478.py',
                            'controls/checker637.py', 'code/checker636.py']:
                add(label, program, json.dumps(four), expected)
            for old, new in [('incoming_tokens244.py', 'checker244.py'), ('incoming_ast267.py', 'checker267.py')]:
                add(label, 'controls/' + old, json_lines(three), expected)
                add(label, 'code/' + new, json_lines(three), expected)

    # These boundaries are deliberately different contracts, not regressions.
    for boundary in ['raw_empty_goal_boundary.json', 'canonical_goal_raw_boundary.json']:
        payload = (ROOT / 'fixtures' / boundary).read_text()
        add(boundary, 'controls/checker479.py', payload, True)
        add(boundary, 'code/checker478.py', payload, False)
    example = json.loads((ROOT / 'fixtures/three_field/local/computation_zero_local.json').read_text())
    add('unread_invalid_suffix', 'code/checker267.py', json_lines(example) + 'not JSON\n', True)
    add('unread_invalid_array_prefix', 'controls/ast270.py', '[not JSON,' + json.dumps(example)[1:], False)

    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(run, tasks))
    summary = dict(python=platform.python_version(), frozen_files=len(provenance['files']),
                   incoming_archive_members=len(incoming['members']),
                   exact_source_transformation_checks=4, generated_computations=len(generated),
                   isolated_executions=len(rows), failed_expectations=sum(not r['passed'] for r in rows))
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    (ROOT / 'evidence/validation.json').write_text(json.dumps(dict(summary=summary, results=rows), indent=2) + '\n')
    print(json.dumps(dict(summary=summary, metrics=metrics), indent=2))
    if summary['failed_expectations']:
        print(json.dumps([r for r in rows if not r['passed']], indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
