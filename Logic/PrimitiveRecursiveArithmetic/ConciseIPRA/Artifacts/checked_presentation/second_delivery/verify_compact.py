"""Finite regressions for scanner binding and certificate streaming.

These checks supplement the universal program equivalence arguments.
The acceptance modules import neither this utility nor their controls.
"""
from pathlib import Path
import concurrent.futures
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(path, payload, optimized=False):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    result = subprocess.run(command + [str(ROOT / path)], input=payload,
                            capture_output=True, timeout=25)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def unstream(payload):
    cells = [json.loads(line) for line in payload.splitlines()]
    return json.dumps(cells[::-1], separators=(',', ':')).encode() + b'\n'


def check_case(task):
    case, optimized = task
    candidate, control = (
        ('code/checker_tokens.py', 'controls/tokens248.py')
        if case['scope'] == 'global' else
        ('code/checker_ast.py', 'controls/ast270.py')
    )
    payload = (ROOT / case['path']).read_bytes()
    return {'fixture': case['path'], 'scope': case['scope'],
            'optimized': optimized, 'expected': case['expected'],
            'control': run(control, unstream(payload), optimized),
            'candidate': run(candidate, payload, optimized)}


def main():
    manifest = json.loads((ROOT / 'evidence/fixture_manifest.json').read_text())
    tasks = [(case, optimized) for case in manifest for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(check_case, tasks))
    byte_rows = []
    payload = (ROOT / 'tests/compact/byte/future_scope_attack.json').read_bytes()
    for program in ['code/checker_bytes.py', 'controls/bytes487.py']:
        for optimized in (False, True):
            byte_rows.append({'program': program, 'optimized': optimized,
                              'fixture': 'future_scope_attack', 'expected': False,
                              'accepted': run(program, payload, optimized)})
    boundary_rows = []
    for program, scope in [('code/checker_tokens.py', 'global'), ('code/checker_ast.py', 'local')]:
        payload = (ROOT / f'tests/compact/{scope}/computation_zero.jsonl').read_bytes()
        cases = [
            ('no_final_newline', payload.rstrip(b'\n'), True),
            ('CRLF', payload.replace(b'\n', b'\r\n'), True),
            ('empty_stream', b'', False),
            ('blank_first_line', b'\n' + payload, False),
            ('goal_without_proof', payload.splitlines()[0] + b'\n', False),
            ('unconsumed_integer_suffix', payload + b'123\n', True),
            ('unconsumed_bytes_outside_frame', payload + b'not JSON\n', True),
            ('two_objects_on_first_line', payload.replace(b'\n', b' []\n', 1), False),
        ]
        for label, stream, expected in cases:
            boundary_rows.append({'program': program, 'case': label,
                                  'expected': expected,
                                  'accepted': run(program, stream)})
        conversion = subprocess.run([sys.executable, '-I', '-S', '-B',
                                     str(ROOT / 'to_stream.py')],
                                    input=unstream(payload), capture_output=True, timeout=10)
        boundary_rows.append({'program': 'to_stream.py', 'case': scope,
                              'expected': True,
                              'accepted': conversion.returncode == 0 and conversion.stdout == payload})
    failures = [r for r in rows if not r['control'] == r['candidate'] == r['expected']]
    failures += [r for r in byte_rows + boundary_rows if r['accepted'] != r['expected']]
    report = {'stream_paired_checker_processes': 2 * len(rows),
              'byte_scope_checker_processes': len(byte_rows),
              'framing_and_converter_processes': len(boundary_rows),
              'failures': failures, 'stream_results': rows,
              'byte_scope_results': byte_rows, 'framing_results': boundary_rows}
    (ROOT / 'evidence/compact_validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if not k.endswith('_results')}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
