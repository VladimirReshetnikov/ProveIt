"""Reproduce the packaged audit and scoped executable evidence offline.

The source corpus is parsed and measured, never imported or executed.
Only the explicitly selected reference checkers and diagnostic scripts run.
"""
from pathlib import Path
import gzip
import importlib.util
import json
import platform
import subprocess
import sys
import zlib

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('metrics', ROOT/'code/measure_sources.py')
metrics = importlib.util.module_from_spec(spec)
spec.loader.exec_module(metrics)


def main():
    recorded = json.loads((ROOT/'evidence/frontier_metrics.json').read_text())
    measured = {}
    candidates = []
    for file in sorted((ROOT/'source_corpus').glob('*.py')):
        raw = file.read_bytes()
        row = metrics.measure(raw)
        if row['sha256'] != file.stem:
            raise ValueError('Source hash mismatch: ' + file.name)
        measured[file.stem] = row
        source = raw.decode('utf-8')
        if 'ACCEPT' in source and ('open(0)' in source or 'stdin' in source):
            candidates.append(row)
    for original in recorded['sources']:
        now = measured[original['sha256']]
        for field, value in now.items():
            if original[field] != value:
                raise ValueError(f'Metric changed: {original["location"]}, {field}')
    fields = ('normalized_bytes', 'normalized_tokens', 'ast_nodes',
              'raw_bytes', 'gzip9_raw_bytes', 'gzip9_normalized_bytes')
    envelope = {field: min(r[field] for r in candidates) for field in fields}
    if envelope != recorded['coordinatewise_minimum']:
        raise ValueError('Coordinate envelope changed')

    selected = json.loads((ROOT/'evidence/selected_sources.json').read_text())
    selected_metrics = {}
    for name in selected:
        raw = (ROOT/'reference'/name).read_bytes()
        row = metrics.measure(raw)
        if row['sha256'] not in measured:
            raise ValueError('Selected source is not in the pinned corpus')
        compressed = gzip.compress(raw, compresslevel=9, mtime=0)
        if compressed != (ROOT/'reference'/(name+'.gz')).read_bytes():
            raise ValueError('Stored gzip stream differs; inspect runtime version')
        selected_metrics[name] = row
    (ROOT/'evidence/selected_metrics.json').write_text(
        json.dumps(selected_metrics, indent=2)+'\n')

    cases = json.loads((ROOT/'tests/byte_leader_cases.json').read_text())['cases']
    payloads = [(c['name'], json.dumps(c['packet']), c['accept']) for c in cases]
    payloads += [('malformed_json', '{', False),
                 ('null_document', 'null', False),
                 ('empty_certificate', '[]', False)]
    byte_runs = []
    for optimized in (False, True):
        for name, payload, expected in payloads:
            command = [sys.executable] + (['-O'] if optimized else [])
            command += [str(ROOT/'reference/byte_leader.py')]
            process = subprocess.run(command, input=payload, text=True,
                                     capture_output=True, timeout=10)
            accepted = process.returncode == 0 and process.stdout.strip() == 'ACCEPT'
            protocol = accepted or (process.returncode != 0
                                    and process.stdout.strip() == 'REJECT')
            if accepted != expected or not protocol:
                raise ValueError('Unexpected reference verdict: ' + name)
            byte_runs.append({'case': name, 'optimized': optimized,
                              'expected': expected, 'accepted': accepted})
    subprocess.run([sys.executable, str(ROOT/'tests/normalization/reproduce.py')],
                   check=True, cwd=ROOT)
    subprocess.run([sys.executable, str(ROOT/'code/unit_collapse.py'),
                    '--output', str(ROOT/'evidence/unit_collapse_results.json')],
                   check=True, cwd=ROOT)
    report = {
        'python': platform.python_version(),
        'zlib_runtime': zlib.ZLIB_RUNTIME_VERSION,
        'commit': recorded['commit'],
        'all_passed': True,
        'distinct_python_sources': len(measured),
        'distinct_driver_candidates': len(candidates),
        'coordinatewise_minimum': envelope,
        'byte_leader_process_runs': len(byte_runs),
        'byte_leader_runs': byte_runs,
        'scope': 'Finite executable evidence and exact source accounting; '
                 'not a formal proof of soundness, completeness, or bi-interpretability.'
    }
    (ROOT/'evidence/reproduction.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'byte_leader_runs'}, indent=2))


if __name__ == '__main__':
    main()
