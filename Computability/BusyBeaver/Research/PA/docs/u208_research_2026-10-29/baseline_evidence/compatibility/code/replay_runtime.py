#!/usr/bin/env python3
"""Replay every arbitrary-natural primitive contract and compare sealed cases."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def need(ok, message):
    if not ok:
        raise ValueError(message)

def summarize(number, report_path, cases_path, compare=True):
    report = json.loads(Path(report_path).read_text())
    cases = json.loads(Path(cases_path).read_text())
    table_path = ROOT / f'machine/u{number}.native.tm'
    source_path = ROOT / f'source/u{number}.sites.json'
    need(report['status'] == 'NATIVE_UNIVERSAL_MATHEMATICAL_PASS', 'Runtime status')
    need(report['table_sha256'] == hashlib.sha256(table_path.read_bytes()).hexdigest(),
         'Runtime table identity')
    need(report['sites_sha256'] == hashlib.sha256(source_path.read_bytes()).hexdigest(),
         'Runtime source identity')
    source = json.loads(source_path.read_text())
    expected = [(i, positive) for i, (_, op, _) in enumerate(source)
                for positive in ((False, True) if op == 'CD' else (False,))]
    need([(c['site_index'], c['positive']) for c in cases] == expected, 'Case inventory')
    need(len(cases) == report['cases'] == 5084, 'Case count')
    rows = {(int(line.split()[0]), int(line.split()[1]))
            for line in table_path.read_text().splitlines() if line and not line.startswith('#')}
    used = {tuple(row) for case in cases for row in case['rows']}
    for block in report['blocks']:
        for event in block['trace']:
            if event[0] != 'list':
                used.add(tuple(event[1][:2]))
    need(used == rows and len(rows) == 2 * number, 'Complete literal-row coverage')
    need(all(len(c['duration']) == 13 and c['duration'][0] > 0
             and all(v >= 0 for v in c['duration']) for c in cases), 'Positive durations')
    if compare:
        with gzip.open(ROOT / f'evidence/u{number}_runtime_cases.json.gz', 'rt') as stream:
            need(cases == json.load(stream), 'Fresh symbolic derivations differ from delivered cases')
    return {'machine': f'U{number}', 'working_states': number, 'transition_rows': len(rows),
            'cases': len(cases), 'row_coverage': len(used),
            'symbolic_inference_applications': sum(c['symbolic_steps'] for c in cases),
            'minimum_duration_constant': min(c['duration'][0] for c in cases),
            'seconds': report['seconds'], 'table_sha256': report['table_sha256'],
            'source_sha256': report['sites_sha256'], 'fresh_derivations_equal_delivered': compare,
            'scope': 'Unary/list-inductive mathematical certificates; not a proof-assistant kernel.'}

def run(number):
    need(__debug__ and not sys.flags.optimize, 'Full runtime requires enabled assertions')
    folder = ROOT / 'build'
    folder.mkdir(exist_ok=True)
    report = folder / f'u{number}_runtime.json'
    subprocess.run([sys.executable, '-B', str(ROOT / 'code/runtime/check_runtime.py'),
                    '--table', str(ROOT / f'machine/u{number}.native.tm'),
                    '--sites', str(ROOT / f'source/u{number}.sites.json'),
                    '--output', str(report)], cwd=ROOT, check=True)
    result = summarize(number, report, report.with_suffix('.cases.json'))
    (folder / f'u{number}_runtime_summary.json').write_text(json.dumps(result, indent=2) + '\n')
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('states', type=int, choices=(209, 210))
    print(json.dumps(run(parser.parse_args().states), indent=2))
