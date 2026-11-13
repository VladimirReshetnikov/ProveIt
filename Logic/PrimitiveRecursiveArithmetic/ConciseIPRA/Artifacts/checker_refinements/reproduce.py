"""Verify the delivered bundle and reproduce its checker measurements."""
import argparse
import hashlib
import json
import platform
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def verify_manifest():
    manifest = ROOT / 'MANIFEST.sha256'
    if not manifest.exists():
        raise SystemExit('MANIFEST.sha256 is missing; use --skip-manifest for a development run.')
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit('Manifest mismatch: ' + name)
        count += 1
    print('Verified SHA-256 manifest for', count, 'files.', flush=True)


def run_script(relative):
    print('Running', relative, flush=True)
    result = subprocess.run([sys.executable, '-I', '-S', '-B', str(ROOT / relative)],
                            cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise SystemExit(result.returncode)
    return json.loads(result.stdout)


def build_pdf():
    compiler = shutil.which('pdflatex')
    if not compiler:
        raise SystemExit('pdflatex is not installed. Checker audits have completed.')
    command = [compiler, '-interaction=nonstopmode', '-halt-on-error',
               'ipra_checker_refinements.tex']
    for number in (1, 2):
        print('Compiling PDF, pass', number, flush=True)
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
    print('Built ipra_checker_refinements.pdf', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='also run pdflatex twice')
    parser.add_argument('--skip-manifest', action='store_true',
                        help='allow intentionally changed generated outputs')
    args = parser.parse_args()
    if not args.skip_manifest:
        verify_manifest()
    if platform.python_version() != '3.12.14':
        print('Reference runtime is CPython 3.12.14; current runtime is',
              platform.python_version(), flush=True)
    baseline = run_script('reference/baseline_audit/measure_selected.py')
    byte = run_script('checkers/byte476/verify476.py')
    node = run_script('checkers/ast269/verify269.py')
    byte_sizes = byte['metrics']['checker476.py']
    expected = [274, 306, 476]
    measured = [byte_sizes[key] for key in ('tokens', 'ast_nodes', 'normalized_bytes')]
    if measured != expected:
        raise SystemExit('Byte-candidate metric mismatch: ' + repr(measured))
    if byte['failures'] or byte['discrepancies'] or node['failed_expectations']:
        raise SystemExit('A verification suite reported failures.')
    receipt = {
        'upstream_commit': baseline['commit'],
        'python': platform.python_version(),
        'selected_baseline_programs': len(baseline['programs']),
        'byte_candidate': byte_sizes,
        'node_candidate': next(m for m in node['metrics'] if m['program'] == 'checker269.py'),
        'byte_suite': {
            'fixture_labels': byte['labelled_fixtures'],
            'unique_payloads': byte['unique_fixture_blobs'],
            'process_executions': byte['process_executions'],
            'failed_expectations': len(byte['failures']),
            'acceptance_discrepancies': len(byte['discrepancies']),
        },
        'node_suite': {
            'fixture_labels': node['fixture_paths'],
            'unique_payloads': node['distinct_fixture_payloads'],
            'process_executions': node['cli_executions'],
            'failed_expectations': node['failed_expectations'],
        },
        'total_process_executions': byte['process_executions'] + node['cli_executions'],
        'all_expectations_passed': True,
        'limits': 'Tests supplement the written proofs; full Python-to-calculus correctness and the arithmetic bridge are inherited.',
    }
    (ROOT / 'verification_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
    if args.pdf:
        build_pdf()


if __name__ == '__main__':
    main()
