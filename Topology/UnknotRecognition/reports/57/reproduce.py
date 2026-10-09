#!/usr/bin/env python3
"""Reproduce the support-kernel research package without changing frozen results.

Quick tests and the frozen-oracle audits use only the Python standard library.
Regina is required only for --regenerate-oracle. Matplotlib and a LaTeX
installation are required only for rebuilding the report.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results'/'reproduced'


def run(args, logname, cwd=ROOT):
    print('Running:', ' '.join(str(x) for x in args), flush=True)
    OUT.mkdir(parents=True, exist_ok=True)
    with (OUT/logname).open('w') as log:
        result = subprocess.run([str(x) for x in args], cwd=cwd,
                                stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print((OUT/logname).read_text()[-6000:], file=sys.stderr)
        raise SystemExit(result.returncode)
    print('  passed; log:', (OUT/logname).relative_to(ROOT), flush=True)


def verify_manifest():
    manifest = ROOT/'MANIFEST.sha256'
    if not manifest.exists():
        raise SystemExit('MANIFEST.sha256 is missing.')
    checked = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT/name
        if not path.is_file() or sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit('Manifest mismatch: '+name)
        checked += 1
    print(f'Manifest verified: {checked} files.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='run the focused public-contract and integration tests')
    parser.add_argument('--audits', action='store_true', help='replay all three audits against the frozen oracle; no Regina required')
    parser.add_argument('--verify-manifest', action='store_true', help='verify every file in the delivered manifest')
    parser.add_argument('--regenerate-oracle', action='store_true', help='separately regenerate fixtures and complete vertex sets with Regina')
    parser.add_argument('--benchmarks', action='store_true', help='rerun paired timings into results/reproduced; do not run other computations concurrently')
    parser.add_argument('--large', action='store_true', help='include the dense 128-tetrahedron benchmark')
    parser.add_argument('--build-pdf', action='store_true', help='rebuild tables, figure and article from frozen timings')
    args = parser.parse_args()
    if not any((args.quick,args.audits,args.verify_manifest,args.regenerate_oracle,args.benchmarks,args.build_pdf)):
        args.quick = True
    py = sys.executable
    if args.verify_manifest:
        verify_manifest()
    if args.quick:
        run([py,'-m','unittest','discover','-s','tests','-v'], 'unit_tests.txt')
        run([py,'-m','unittest','discover','-s','fast/tests','-p','test_normal_sector_integration.py','-v'],
            'integration_tests.txt')
    if args.audits:
        for stem in ('audit_sector','audit_support_method','audit_sector_certificates'):
            output = OUT/(stem+'.json')
            run([py,ROOT/'scripts'/(stem+'.py'),'--fast',ROOT/'fast',
                 '--corpus',ROOT/'results'/'discovery_corpus.json',
                 '--cases',ROOT/'results'/'sector_cases.json','--output',output], stem+'.txt')
            report = json.loads(output.read_text())
            if stem == 'audit_sector':
                statuses = [p['status'] for r in report['records'] for p in r['phases'].values()]
                if len(statuses) != 3436 or any(s != 'PASS' for s in statuses):
                    raise SystemExit('The full frozen-oracle audit was not completed: inspect '+str(output))
            print(json.dumps(report['summary'],indent=2),flush=True)
    if args.regenerate_oracle:
        corpus, cases = OUT/'discovery_corpus.json', OUT/'sector_cases.json'
        run([py,ROOT/'scripts'/'discovery_corpus.py','--output',corpus], 'oracle_generation.txt')
        run([py,ROOT/'scripts'/'sector_reference.py','--corpus',corpus,'--output',cases],
            'oracle_selection.txt')
        run([py,ROOT/'scripts'/'fibonacci_fixture.py'], 'fibonacci_fixture_check.json')
        print('The regenerated oracle is separate from the frozen one; its labels and timings may differ.',flush=True)
    if args.benchmarks:
        command = [py,ROOT/'scripts'/'benchmark.py','--output',OUT/'benchmarks.json']
        if args.large:
            command.append('--large')
        run(command,'benchmarks.txt')
    if args.build_pdf:
        run([py,ROOT/'scripts'/'make_measurement_tables.py'],'measurement_tables.txt')
        for i in range(1,6):
            run(['pdflatex','-interaction=nonstopmode','-halt-on-error','article.tex'],
                f'pdflatex_{i}.txt',cwd=ROOT/'article')
            log = (OUT/f'pdflatex_{i}.txt').read_text()
            if not any(message in log for message in (
                    'Rerun to get', 'Label(s) may have changed', 'Please rerun')):
                break
        else:
            raise SystemExit('LaTeX references did not stabilize after five passes.')
        print('Built article/article.pdf. This rebuild changes the delivered PDF hash.',flush=True)


if __name__ == '__main__':
    main()
