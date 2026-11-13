"""Portable subprocess verification of strict packet-prefix conjugacy."""

import concurrent.futures
import json
from pathlib import Path
import subprocess
import sys

from translate_certificates import rotate_packets

ROOT = Path(__file__).resolve().parent.parent


def run(job):
    name, certificate, expected, candidate, optimized = job
    script = ROOT / ('code/checker_strict599.py' if candidate
                     else 'controls/strict_bytes600.py')
    if candidate:
        certificate = rotate_packets(certificate)
    process = subprocess.run(
        [sys.executable, *(['-O'] if optimized else []), str(script)],
        input=json.dumps(certificate), text=True, capture_output=True, timeout=20,
    )
    accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
    return dict(case=name, checker=str(script.relative_to(ROOT)),
                optimized=optimized, expected=expected, accepted=accepted)


def main():
    data = json.loads((ROOT / 'examples/strict_cases.json').read_text())
    jobs = [(case['name'], case['certificate'], case['expected'], candidate, optimized)
            for case in data['cases'] for candidate in (False, True)
            for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(run, jobs))
    failures = [row for row in rows if row['expected'] != row['accepted']]
    summary = {'executions': len(rows), 'cases': len(data['cases']),
               'failures': failures, 'results': rows,
               'certificate_source': data['source']}
    (ROOT / 'evidence/strict_validation.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit('Strict checker validation failed')


if __name__ == '__main__':
    main()
