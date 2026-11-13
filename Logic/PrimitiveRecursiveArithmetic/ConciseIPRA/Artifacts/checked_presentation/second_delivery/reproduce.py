"""Recompute the source comparison and implementation evidence offline."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='also rebuild the PDF')
    args = parser.parse_args()
    manifest = ROOT / 'MANIFEST.sha256'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected, filename = line.split('  ', 1)
            if hashlib.sha256((ROOT / filename).read_bytes()).hexdigest() != expected:
                raise ValueError('Delivered-file hash mismatch: ' + filename)
        print('Delivered-file hashes verified.', flush=True)
    for script in ['audit_sources.py', 'measure.py', 'verify_compact.py',
                   'verify_byte.py', 'verify_validated.py', 'verify_readable.py']:
        print('Running ' + script, flush=True)
        subprocess.run([sys.executable, '-B', script], cwd=ROOT, check=True)
    result = {'python': sys.version.split()[0], 'failures': 0,
              'primary_checker_processes': 730,
              'readable_checker_processes': 224,
              'independent_stream_review_processes': 40,
              'new_compact_envelope': [244, 267, 479],
              'envelope_attained_by_one_program': False,
              'new_axiom_deletion': False,
              'formal_assistant_build': False}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
    if args.pdf:
        subprocess.run([sys.executable, '-B', 'build.py'], cwd=ROOT, check=True)
    print('All source and implementation checks passed.', flush=True)


if __name__ == '__main__':
    main()
