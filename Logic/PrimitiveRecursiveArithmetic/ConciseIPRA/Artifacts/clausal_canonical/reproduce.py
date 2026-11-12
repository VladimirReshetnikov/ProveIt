"""Rebuild measurements, run verification, and optionally compile the report."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(*arguments):
    subprocess.run(arguments, cwd=ROOT, check=True)


def verify_sources():
    provenance = json.loads((ROOT / 'evidence/source_provenance.json').read_text())
    for item in provenance['files']:
        contents = (ROOT / item['path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(contents)).encode() + b'\0' + contents).hexdigest()
        if blob != item['git_blob'] or hashlib.sha256(contents).hexdigest() != item['sha256']:
            raise ValueError('Source identity mismatch: ' + item['path'])
    print('Pinned source identities verified.', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    options = parser.parse_args()
    verify_sources()
    for script in ('tools/build_control.py', 'tools/measure.py',
                   'tests/verify_one_term.py', 'tests/verify_clausal.py',
                   'tests/verify_arity.py', 'tests/test_arity_audit.py'):
        run(sys.executable, script)
    run(sys.executable, 'tools/build_report.py')
    if options.pdf:
        for _ in range(3):
            run('pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'report.tex')
    print('Reproduction completed successfully.')


if __name__ == '__main__':
    main()
