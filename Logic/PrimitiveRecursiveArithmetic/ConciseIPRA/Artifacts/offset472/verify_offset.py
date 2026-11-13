"""Reproduce the offset-depth checker comparison; standard library only."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}


def normalized(text):
    return ast.unparse(ast.parse(text)) + '\n'


def metrics(path):
    source = normalized(path.read_text())
    return {'file': path.name,
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(source)))),
            'normalized_bytes': len(source.encode()),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def shift_tree(tree):
    """Shift positive slot coordinates; zero and rigid names stay fixed."""
    if type(tree) is list:
        return [shift_tree(child) for child in tree]
    if type(tree) is int and tree > 0:
        return tree + 2
    return tree


def translate(certificate):
    """Translate canonical integer/list certificates, preserving bad fixtures."""
    result = shift_tree(certificate)
    for packet in result[:-1]:
        if type(packet) is list and len(packet) == 4 and packet[0] == []:
            packet[0] = 0
    return result


def execute(job):
    name, filename, optimized, data, expected = job
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / filename))
    result = subprocess.run(command, input=data, capture_output=True, timeout=15)
    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return {'case': name, 'program': filename, 'optimized': optimized,
            'expected': expected, 'accepted': accepted, 'passed': accepted == expected}


def main():
    original = (ROOT / 'control473.py').read_text()
    changes = [('d=0:', 'd=2:'), ('d=3', 'd=5'),
               ('i(t, [s, u, t], 3)', 'i(t, [s, u, t], 5)'),
               ('i(*a, t, 2)', 'i(*a, t, 4)'),
               ('c([[]], *q())', 'c([0], *q())')]
    candidate = original
    for before, after in changes:
        if candidate.count(before) != 1:
            raise ValueError(f'Expected exactly one occurrence of {before!r}')
        candidate = candidate.replace(before, after)
    if (ROOT / 'offset472.py').read_text() != normalized(candidate):
        raise ValueError('Unexpected candidate source')

    fixtures = ROOT / 'fixtures_original'
    cases = json.loads((fixtures / 'cases.json').read_text())
    cases.append({'file': 'direct_zero_seed.json', 'expected': True})
    prepared = []
    for case in cases:
        name, expected = case['file'], case['expected']
        certificate = json.loads((fixtures / name).read_bytes())
        prepared.append((name, certificate, expected))
        if expected:
            false_goal = json.loads(json.dumps(certificate))
            false_goal[-1] = [[0, [0]], 0]
            prepared.append(('false_goal_' + name, false_goal, False))

    jobs = []
    for name, certificate, expected in prepared:
        for filename, data in [('control473.py', certificate),
                               ('offset472.py', translate(certificate)),
                               ('checker_readable.py', translate(certificate))]:
            encoded = json.dumps(data, separators=(',', ':')).encode()
            for optimized in [False, True]:
                jobs.append((name, filename, optimized, encoded, expected))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(execute, jobs))
    failures = [r for r in results if not r['passed']]
    report = {'python': sys.version, 'exact_declared_edits': True,
              'source_changes': changes,
              'metrics': [metrics(ROOT / 'control473.py'), metrics(ROOT / 'offset472.py')],
              'cases': len(prepared), 'executions': len(results),
              'failures': failures, 'results': results,
              'limits': ['Finite regression evidence, not a soundness proof.',
                         'The public formula alphabet and grammar are promised by the compact input contract.',
                         'Full metatheoretic soundness and completeness use the shifted sorted reading.']}
    (ROOT / 'offset_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
