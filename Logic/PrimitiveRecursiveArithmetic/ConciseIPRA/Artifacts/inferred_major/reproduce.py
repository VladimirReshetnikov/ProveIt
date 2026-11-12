"""Verify the delivered proof-checker package; optionally rebuild its PDF."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    sources = json.loads((ROOT / 'evidence/source_provenance.json').read_text())
    for item in sources['sources']:
        data = (ROOT / item['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != item['git_blob_sha']:
            raise ValueError('Pinned source hash mismatch: ' + item['local'])
    subprocess.run([sys.executable, 'verify.py'], cwd=ROOT / 'code', check=True)
    shutil.copyfile(ROOT / 'code/verification.json', ROOT / 'evidence/validation.json')
    subprocess.run([sys.executable, 'build_report.py'], cwd=ROOT, check=True)
    if args.pdf:
        subprocess.run([sys.executable, 'build_pdf.py'], cwd=ROOT, check=True)
    print('PASS: sources, complete checkers, metrics and executable evidence.')


if __name__ == '__main__':
    main()
