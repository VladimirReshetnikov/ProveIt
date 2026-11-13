"""Reproduce the independent checks without network or external repositories.

Run from any directory with CPython 3.12. The script locates this package by
its own path. It checks exactly the supplied fixture corpus, validates fixture
hashes, executes both controls and candidates normally and under -O, and writes
evidence/independent_validation.json. Acceptance checks run the complete checker
files in isolated subprocesses. Secondary instrumented runs compare record traces.
"""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent.parent
SKIP = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
        tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
PROVENANCE = json.loads((ROOT / 'fixtures/independent/provenance.json').read_text())
EXPECTED = json.loads((ROOT / 'evidence/independent_audit_summary.json').read_text())


def measure(path):
    code = (ast.unparse(ast.parse(path.read_bytes())) + '\n').encode()
    return {'file': path.name,
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(code.decode()).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(code))),
            'bytes': len(code), 'gzip9': len(gzip.compress(code, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(code).hexdigest()}


def execute(path, text, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(path))
    result = subprocess.run(command, input=text, text=True, capture_output=True, timeout=15)
    return {'accepted': result.returncode == 0 and result.stdout == 'ACCEPT\n',
            'exception': result.stderr.splitlines()[-1].split(':')[0] if result.stderr else None}


def trace(path, records):
    remaining = copy.deepcopy(records)
    reads, output = [], []

    def take():
        value = remaining.pop(0)
        reads.append(copy.deepcopy(value))
        return json.dumps(value)

    namespace = {'input': take, 'print': lambda *args: output.append(args)}
    try:
        exec(compile(path.read_text(), str(path), 'exec'), namespace)
        outcome = 'return'
    except BaseException as error:
        outcome = type(error).__name__
    return outcome, reads, remaining, namespace.get('k'), output


def rotated_packets(certificate):
    # The final root header, including its public goal, is unchanged.
    return [row[1:] + row[:1] if isinstance(row, list) and len(row) == 4 else row
            for row in certificate[:-1]] + [certificate[-1]]


def main():
    groups = {'stream': [], 'bytes': []}
    for entry in PROVENANCE['fixtures']:
        data = (ROOT / entry['file']).read_bytes()
        if hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise ValueError('Fixture hash mismatch: ' + entry['file'])
        records = [json.loads(line) for line in data.decode().splitlines()] if entry['kind'] == 'stream' else json.loads(data)
        groups[entry['kind']].append((entry, records))

    configurations = [
        ('tokens239', 'raw_stream_tokens240.py', 'checker_tokens239.py', 'stream'),
        ('ast257', 'raw_stream_tokens240.py', 'checker_ast257.py', 'stream'),
        ('tokens244whole', 'matched_return_whole245.py', 'checker_tokens244.py', 'whole'),
        ('ast261whole', 'matched_return_whole245.py', 'checker_ast261.py', 'whole'),
        ('bytes461', 'raw_whole_bytes462.py', 'checker_bytes461.py', 'bytes'),
    ]
    results, traces = [], []
    for profile, control_name, candidate_name, framing in configurations:
        control = ROOT / 'controls' / control_name
        candidate = ROOT / 'code' / candidate_name
        for entry, records in groups['bytes' if framing == 'bytes' else 'stream']:
            if framing == 'bytes':
                left_text, right_text = json.dumps(records), json.dumps(rotated_packets(records))
            elif framing == 'whole':
                left_text = right_text = json.dumps(list(reversed(records)))
            else:
                left_text = right_text = ''.join(json.dumps(row) + '\n' for row in records)
            for optimized in (False, True):
                left = execute(control, left_text, optimized)
                right = execute(candidate, right_text, optimized)
                results.append({'profile': profile, 'fixture': entry['file'],
                                'optimized': optimized, 'expected': entry['expected'],
                                'control': left, 'candidate': right,
                                'passed': left['accepted'] == right['accepted'] == entry['expected']})
            if framing == 'stream':
                left, right = trace(control, records), trace(candidate, records)
                # Tuple unpacking and pattern matching can raise different
                # exception classes for malformed records. Both must reject.
                same = left[1:] == right[1:] and (left[0] == 'return') == (right[0] == 'return')
                traces.append({'profile': profile, 'fixture': entry['file'],
                               'equivalent_trace': same,
                               'same_exception_class': left[0] == right[0],
                               'consumed_records': len(right[1])})

    metrics = [measure(ROOT / 'code' / row['file']) for row in EXPECTED['metrics']]
    metric_failures = [actual for actual, expected in zip(metrics, EXPECTED['metrics']) if actual != expected]
    failures = [row for row in results if not row['passed']]
    failures += [row for row in traces if not row['equivalent_trace']]
    report = {'python': sys.version, 'snapshot': PROVENANCE['snapshot'],
              'fixtures': len(PROVENANCE['fixtures']), 'metrics': metrics,
              'paired_comparisons': len(results), 'executions': 2 * len(results),
              'trace_comparisons': len(traces), 'failures': failures,
              'metric_failures': metric_failures, 'results': results, 'traces': traces,
              'scope': 'Finite verification of the stated operational correspondences; the written proofs establish the universal claims.'}
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/independent_validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key:value for key,value in report.items() if key not in ('results', 'traces')}, indent=2))
    if failures or metric_failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
