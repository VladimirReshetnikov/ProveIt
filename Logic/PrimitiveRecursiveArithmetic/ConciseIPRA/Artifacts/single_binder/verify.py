"""Offline finite regressions; the acceptance modules never import this file."""
from pathlib import Path
import concurrent.futures
import hashlib
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PROGRAMS = {
    'tokens': ('controls/tokens_control.py', 'code/tokens248.py'),
    'ast': ('controls/ast_control.py', 'code/ast270.py'),
    'bytes': ('controls/bytes_control.py', 'code/bytes487.py'),
    'bytes_readable': ('controls/bytes_control.py', 'code/bytes488.py'),
}


def run(program, payload, optimized=False):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    result = subprocess.run(command + [str(ROOT / program)], input=payload,
                            capture_output=True, timeout=25)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def serialized(data):
    return json.dumps(data, separators=(',', ':'), ensure_ascii=True).encode() + b'\n'


def compare(task):
    name, path, optimized = task
    control, candidate = PROGRAMS[name]
    payload = path.read_bytes()
    data = json.loads(payload)
    return {'profile': name, 'fixture': str(path.relative_to(ROOT)),
            'optimized': optimized,
            'control': run(control, payload, optimized),
            'candidate': run(candidate, serialized(data), optimized)}


def main():
    manifest = json.loads((ROOT / 'evidence/source_fixtures.json').read_text())
    for item in manifest['files']:
        if hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() != item['sha256']:
            raise ValueError('A frozen fixture differs from its source hash')
    tasks = []
    for name in PROGRAMS:
        if name in ('tokens', 'ast'):
            scope = 'global' if name == 'tokens' else 'local'
            files = sorted((ROOT / 'tests/three_field' / scope).glob('*.json'))
            files += sorted((ROOT / 'tests/three_field/adversarial').glob('*.json'))
        else:
            files = sorted((ROOT / 'tests/byte').rglob('*.json'))
        for path in files:
            for optimized in (False, True):
                tasks.append((name, path, optimized))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(compare, tasks))

    # Independent boundary examples for the extra strict public interface.
    minimal = json.loads((ROOT / 'tests/byte/context/computation_zero_local.json').read_text())
    strict_cases = [
        ('zero_computation', minimal, True),
        ('empty_certificate', [], False),
        ('false_equation', [[0, [0]]], False),
        ('scalar_goal', [0], False),
        ('unbound_positive_goal', [[3, 3]], False),
        ('unbound_negative_goal', [[-1, -1]], False),
        ('unguarded_D_goal', [[[5, 5]]], False),
        ('public_Q_goal', [[[0, 0], [0, 0], [0, 0]]], False),
        ('unused_boolean', [True] + minimal, False),
        ('unused_float', [0.0] + minimal, False),
        ('unused_object', [{}] + minimal, False),
        ('unused_string', ['unused'] + minimal, False),
        ('unused_null', [None] + minimal, False),
    ]
    for name in ['computation_successor_local.json', 'transport_reflexivity_local.json',
                 'guarded_literal_equation_introduction_local.json',
                 'guarded_lift_elimination_local.json']:
        strict_cases.append((name, json.loads((ROOT/'tests/byte/context'/name).read_text()), True))
    for name in ['future_witness_capture.json', 'context_leak_attack.json',
                 'false_float_capture.json']:
        strict_cases.append((name, json.loads((ROOT/'tests/byte/context'/name).read_text()), False))
    strict_rows = []
    for name, data, expected in strict_cases:
        for optimized in (False, True):
            accepted = run('code/strict_guarded.py', serialized(data), optimized)
            strict_rows.append({'fixture': name, 'optimized': optimized,
                                'expected': expected, 'accepted': accepted})

    # The single-line format deliberately ignores later physical lines.
    # These are boundary-contract checks, not assertions of whole-file equivalence.
    first_global = next((ROOT/'tests/three_field/global').glob('*.json'))
    data = json.loads(first_global.read_text())
    one_line = serialized(data)
    framing = []
    for label, payload, expected in [
        ('no_final_newline', one_line.rstrip(b'\n'), True),
        ('CRLF', one_line.rstrip(b'\n') + b'\r\n', True),
        ('blank_first_line', b'\n' + one_line, False),
        ('later_line_is_outside_frame', one_line + b'not JSON\n', True),
        ('two_documents_on_first_line', one_line.rstrip(b'\n') + b' []\n', False),
    ]:
        actual = run('code/tokens248.py', payload)
        framing.append({'case': label, 'expected': expected, 'accepted': actual})
    convert = subprocess.run([sys.executable, str(ROOT/'code/to_one_line.py')],
                             input=first_global.read_bytes(), capture_output=True, timeout=10)
    conversion_ok = (convert.returncode == 0 and
                     json.loads(convert.stdout) == data and
                     convert.stdout.count(b'\n') == 1)
    mismatches = [row for row in rows if row['control'] != row['candidate']]
    strict_failures = [row for row in strict_rows if row['expected'] != row['accepted']]
    framing_failures = [row for row in framing if row['expected'] != row['accepted']]
    report = {'python': platform.python_version(),
              'fixtures_by_profile': {name: sum(row['profile'] == name for row in rows)//2
                                      for name in PROGRAMS},
              'comparison_process_executions': 2 * len(rows),
              'strict_process_executions': len(strict_rows),
              'framing_process_executions': len(framing),
              'converter_process_executions': 1,
              'mismatches': mismatches, 'strict_failures': strict_failures,
              'framing_failures': framing_failures, 'converter_round_trip': conversion_ok,
              'results': rows, 'strict_results': strict_rows, 'framing_results': framing,
              'assurance': 'Finite regressions supplement the universal transformation proof.'}
    (ROOT/'evidence/validation.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({key:value for key,value in report.items()
                     if key not in ('results','strict_results','framing_results')}, indent=2))
    if mismatches or strict_failures or framing_failures or not conversion_ok:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
