"""Finite CLI verification of the scalar-freshness candidate.

The checker imports none of this tooling. The injected constant-name
program is a deliberately unsound negative control kept only in a temporary
directory; a false canonical theorem must distinguish it from the candidate.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tokenize

from translate import Translation, read_stream, write_stream

ROOT = Path(__file__).resolve().parent
sys.set_int_max_str_digits(0)
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL,
        tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    code = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {'file': path.name,
            'significant_tokens': sum(t.type not in SKIP for t in
                                      tokenize.generate_tokens(io.StringIO(code).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(code)))),
            'normalized_bytes': len(code.encode()),
            'normalized_sha256': hashlib.sha256(code.encode()).hexdigest()}


def run(path, data, optimized):
    args = [sys.executable, '-I', '-S', '-B', '-X', 'int_max_str_digits=0']
    if optimized:
        args.append('-O')
    p = subprocess.run(args + [str(path)], input=data, capture_output=True,
                       timeout=20)
    return {'accepted': p.returncode == 0 and p.stdout == b'ACCEPT\n',
            'exit_code': p.returncode,
            'last_error': p.stderr.decode().splitlines()[-1] if p.stderr else ''}


def main():
    cases = []
    translations = []
    for source in sorted((ROOT / 'fixtures').glob('*_source.jsonl')):
        name = source.name.removesuffix('_source.jsonl')
        t = Translation(read_stream(source))
        rows = t.run()
        destination = ROOT / 'fixtures' / (name + '.jsonl')
        write_stream(destination, rows)
        data = destination.read_bytes()
        translations.append({'name': name, 'packets': t.cursor - 1,
                             'bytes': len(data), 'allocations': t.allocations,
                             'events': t.events})
        for optimized in (False, True):
            cases.append({'name': name, 'kind': 'translated-positive',
                          'optimized': optimized, 'expected': True,
                          **run(ROOT / 'checker.py', data, optimized)})
            false_data = b'[0,[0]]\n' + data.split(b'\n', 1)[1]
            cases.append({'name': name, 'kind': 'false-root-mutation',
                          'optimized': optimized, 'expected': False,
                          **run(ROOT / 'checker.py', false_data, optimized)})
        original = run(ROOT / 'control239.py', source.read_bytes(), False)
        cases.append({'name': name, 'kind': 'source-control',
                      'expected': True, **original})

    for fixture in sorted((ROOT / 'fixtures').glob('reject_*.jsonl')):
        for optimized in (False, True):
            cases.append({'name': fixture.stem, 'kind': 'rejection-control',
                          'optimized': optimized, 'expected': False,
                          **run(ROOT / 'checker.py', fixture.read_bytes(), optimized)})

    with tempfile.TemporaryDirectory() as directory:
        bad = Path(directory) / 'UNSOUND_fixed_name.py'
        source = (ROOT / 'checker.py').read_text()
        bad.write_text(source.replace('k = -10 ** len(str([g, a, r]))', 'k = -1'))
        data = (ROOT / 'fixtures/reject_fixed_scalar_capture.jsonl').read_bytes()
        for optimized in (False, True):
            cases.append({'name': 'fixed-scalar-capture', 'kind': 'UNSOUND-control',
                          'optimized': optimized, 'expected': True,
                          **run(bad, data, optimized)})

    failures = [c for c in cases if c['accepted'] != c['expected']]
    report = {'python': sys.version, 'resource_setting': '-X int_max_str_digits=0',
              'metrics': [measure(ROOT / 'checker.py'), measure(ROOT / 'control239.py')],
              'executions': len(cases), 'failed_expectations': len(failures),
              'translations': translations, 'results': cases,
              'scope': 'Finite regression evidence, not a universal soundness proof.',
              'growth_limit': 'The large inherited guarded-induction fixture exceeded the '
                              'untrusted producer diagnostic cap of 2000000 decimal digits. '
                              'That cap is not part of the checker.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('metrics', 'executions', 'failed_expectations')}, indent=2))
    if failures:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
