"""Run the portable verification and size measurements, optionally rebuild PDF."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(*arguments):
    result = subprocess.run([sys.executable, *arguments], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    print(arguments[0] + ': passed')


def check_manifest():
    path = ROOT / 'MANIFEST.json'
    manifest = json.loads(path.read_text())
    for name, expected in manifest['sha256'].items():
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit('Manifest mismatch: ' + name)
    print('Manifest: ' + str(len(manifest['sha256'])) + ' files verified')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    parser.add_argument('--check-manifest', action='store_true')
    options = parser.parse_args()
    if options.check_manifest:
        check_manifest()
    run('code/measure.py')
    run('code/audit.py', '--checker', str(ROOT / 'code/checker.py'),
        '--output', str(ROOT / 'evidence/independent_audit.json'))
    run('code/verify_examples.py', '--write')
    if options.pdf:
        run('build_report.py')
        run('build_pdf.py')
    metrics = json.loads((ROOT / 'evidence/metrics.json').read_text())
    selected = metrics['programs']['selected_uniform_R']
    print('Selected complete module: {normalized_bytes} bytes, '
          '{significant_tokens} tokens, {ast_nodes} AST, '
          '{normalized_gzip9_bytes} gzip-9 bytes.'.format(**selected))
    print('All requested reproduction steps passed.')


if __name__ == '__main__':
    main()

