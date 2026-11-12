"""Run complete candidate programs on independently produced certificates.

The tests execute each whole program in a subprocess. Producer code is never
imported by a checker. The checked stdout/exit protocol is part of the test.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kernel', type=Path, nargs='+')
    parser.add_argument('--cases', type=Path, default=Path(__file__).with_name('cases.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('results.json'))
    args = parser.parse_args()
    cases = json.loads(args.cases.read_text())['cases']
    records = []
    for kernel in args.kernel:
        kernel = kernel.resolve()
        for case in cases:
            result = subprocess.run([sys.executable, str(kernel)],
                                    input=json.dumps(case['packet']), text=True,
                                    capture_output=True, timeout=30)
            accepted = result.stdout.strip() == 'ACCEPT' and result.returncode == 0
            protocol = ((result.stdout.strip() == 'ACCEPT' and result.returncode == 0)
                        or (result.stdout.strip() == 'REJECT' and result.returncode != 0))
            record = {'kernel': str(kernel), 'name': case['name'],
                      'expected': case['accept'], 'accepted': accepted,
                      'protocol_valid': protocol,
                      'passed': accepted == case['accept'] and protocol,
                      'packet_cells': len(case['packet']),
                      'exit_code': result.returncode,
                      'stdout': result.stdout.strip()}
            if not record['passed']:
                record['stderr'] = result.stderr[-3000:]
            records.append(record)
    report = {
        'scope': 'Finite executable validation; no formal metatheorem is implied.',
        'kernels': [{'path': str(p.resolve()),
                     'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in args.kernel],
        'cases_sha256': hashlib.sha256(args.cases.read_bytes()).hexdigest(),
        'tests': len(records), 'passed': sum(r['passed'] for r in records),
        'results': records,
    }
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'tests': report['tests'], 'passed': report['passed'],
                      'failures': [r for r in records if not r['passed']]}, indent=2))
    if report['passed'] != report['tests']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
