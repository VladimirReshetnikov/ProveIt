"""Measure and verify the stream-pattern and whole-JSON profile changes."""
import ast
import dis
import io
import json
from pathlib import Path
import subprocess
import sys

from translate_stream import to_lines, to_whole
from verify import measure

ROOT = Path(__file__).resolve().parent
PROGRAMS = ['control_tokens241_jsonl.py', 'control_ast262_jsonl.py',
            'checker_ast_jsonl.py', 'checker_tokens_json.py',
            'checker_ast_json.py']


def run(name, data, optimized):
    flags = ['-I', '-S', '-B'] + (['-O'] if optimized else [])
    r = subprocess.run([sys.executable, *flags, str(ROOT / name)],
                       input=data, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=30)
    return {'accepted': r.returncode == 0 and r.stdout == b'ACCEPT\n',
            'exception': r.stderr.decode(errors='replace').splitlines()[-1]
                         if r.stderr else ''}


def main():
    rows = []
    for path in sorted((ROOT / 'stream_fixtures').glob('*.jsonl')):
        text = path.read_text()
        positive = path.name.startswith('global_') or path.name == 'direct_successor_zero_initializer.jsonl'
        records = [json.loads(line) for line in text.splitlines()]
        assert [json.loads(line) for line in to_lines(to_whole(text)).splitlines()] == records
        cases = [(path.name, text, positive)]
        if positive:
            cases.append(('false_goal__' + path.name,
                          '[0,[0]]\n' + text.split('\n', 1)[1], False))
        for label, data, expected in cases:
            whole = json.dumps(to_whole(data)).encode()
            for optimized in (False, True):
                results = {name: run(name, data.encode() if name.endswith('_jsonl.py') else whole,
                                     optimized) for name in PROGRAMS}
                assert all(r['accepted'] == expected for r in results.values()), (label, results)
                rows.append({'case': label, 'optimized': optimized,
                             'expected': expected, 'results': results})

    # A malformed packet must reject even for an immediate hypothesis leaf.
    # This directly tests the eager use of all pattern-bound local names.
    for packet in [0, [], [0], [0, 0], [0, 0, 0, 0], [[], [], [], []],
                   [[0], [0], [0], [0]], [0, 0, 0, 0, 0]]:
        lines = '0\n' + json.dumps(packet) + '\n'
        whole = json.dumps(to_whole(lines)).encode()
        results = {name: run(name, lines.encode() if name.endswith('_jsonl.py') else whole,
                             False) for name in PROGRAMS}
        assert all(not r['accepted'] for r in results.values()), (packet, results)
        rows.append({'case': 'malformed-packet-on-neutral-leaf',
                     'packet': packet, 'results': results, 'expected': False})

    # Exact arity succeeds at that same neutral leaf.
    lines = '0\n[0,0,0]\n'
    results = {name: run(name, lines.encode() if name.endswith('_jsonl.py') else
                         json.dumps(to_whole(lines)).encode(), False) for name in PROGRAMS}
    assert all(r['accepted'] for r in results.values())
    rows.append({'case': 'exact-arity-neutral-leaf', 'results': results, 'expected': True})

    names = PROGRAMS + ['control_tokens248_json.py', 'control_ast268_json.py']
    report = {'python': sys.version,
              'metrics': {name: measure(ROOT / name) for name in names},
              'tests': rows, 'process_executions': sum(len(r['results']) for r in rows),
              'all_expectations_met': True,
              'proof_status': 'Written finite trace equivalence and CPython 3.12 pattern-binding argument; finite tests are supporting evidence.'}
    (ROOT / 'profiles_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'metrics': report['metrics'],
                      'process_executions': report['process_executions'],
                      'all_expectations_met': True}, indent=2))


if __name__ == '__main__':
    main()
