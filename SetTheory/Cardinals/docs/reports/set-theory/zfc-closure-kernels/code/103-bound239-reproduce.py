#!/usr/bin/env python3
"""Replay the packaged certificates in an isolated temporary copy.

The default run checks finite certificates, literal construction, the complete
blank prefix, and all minimum-register instruction fixtures.  --full also
rederives the three unbounded runtime results.  Python standard library only.
All archived records remain untouched.  Assertions must be enabled.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true',
                        help='also rerun all three universal runtime checks')
    parser.add_argument('--record', type=Path, help='save this replay summary')
    parser.add_argument('--keep-work', type=Path,
                        help='use and keep a NEW directory instead of temporary storage')
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run Python without -O or -OO.')
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required.')

    manifest = ROOT / 'SHA256SUMS'
    checked = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected, relative = line.split('  ', 1)
            path = ROOT / relative
            require(path.is_file(), f'Missing manifest entry: {relative}')
            require(digest(path) == expected, f'Manifest mismatch: {relative}')
            checked += 1
    print(f'Manifest: {checked} files verified.', flush=True)

    temporary = None
    if args.keep_work:
        work = args.keep_work.resolve()
        require(not work.exists(), '--keep-work must name a new directory.')
    else:
        temporary = tempfile.TemporaryDirectory(prefix='zfc239-replay-')
        work = Path(temporary.name) / 'bundle'
    shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    logs = work / 'replay-logs'
    logs.mkdir(exist_ok=True)
    results = []
    started = time.monotonic()

    def run(label, arguments):
        begin = time.monotonic()
        print(f'Checking {label} ...', flush=True)
        command = [sys.executable, '-B', *arguments]
        answer = subprocess.run(command, cwd=work, capture_output=True, text=True)
        (logs / f'{label}.log').write_text(answer.stdout + answer.stderr)
        if answer.returncode:
            print(answer.stdout[-4000:] + answer.stderr[-4000:], file=sys.stderr)
            raise RuntimeError(f'{label} failed with exit code {answer.returncode}')
        results.append({'check': label, 'status': 'PASS',
                        'seconds': round(time.monotonic() - begin, 3),
                        'arguments': arguments})
        return answer.stdout

    try:
        run('source_rotation', ['formalism/extra/check_rotation_certificate.py'])
        run('baseline_table_and_start', ['validation/check_baseline.py'])
        run('literal_239_construction', ['candidate239/build_candidate239.py'])
        run('exact_lean_source_and_seed', ['source_interface/check_source_interface.py'])
        require(digest(work / 'candidate239/zfc_boundary239_old.tm') ==
                'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719',
                'Reconstructed inherited table has the wrong hash.')
        require(digest(work / 'candidate239/zfc_boundary239.tm') ==
                '666f5bf1370b6b44ff4e614e4b194bc5be6b4c621914842ad7e344d6570a544e',
                'Reconstructed canonical table has the wrong hash.')
        run('six_block_fold', ['state_folds/certify_239_fold.py',
            'boundary240/boundary240_old.tm', 'candidate239/zfc_boundary239_old.tm',
            '--output', 'replay-logs/six_block_fold.json'])
        certificate = json.loads((logs / 'six_block_fold.json').read_text())
        require(certificate['status'] == 'PASS', 'The six-block certificate did not pass.')
        run('final_minimum_fixtures', ['source_encoding/finite_screen.py',
            'candidate239/zfc_boundary239_old.tm', 'candidate239/sites_logical.json',
            '--output', 'replay-logs/final_minimum_fixtures.json'])
        fixtures = json.loads((logs / 'final_minimum_fixtures.json').read_text())
        require((fixtures['cases'], fixtures['failed']) == (8386, 0),
                'The final minimum-register fixtures differ from 8386/0.')
        run('abstract_source_invariant', ['semantic/abstract_zeros.py'])
        diagnostic = json.loads(run('flat_container_diagnostic',
                                    ['formalism/check_flat_container.py']))
        require(diagnostic['root_witnesses'] == 256 and diagnostic['status'] == 'PASS',
                'The finite model diagnostic did not pass.')

        if args.full:
            jobs = [
                ('baseline_unbounded', ['validation/symbolic_runtime.py'],
                 'validation/baseline240_universal.json', 2322575),
                ('boundary240_unbounded', ['validation/check_boundary240.py'],
                 'boundary240/universal_runtime.json', 2252241),
                ('final239_unbounded', ['validation/check_literal_runtime.py',
                    '--table', 'candidate239/zfc_boundary239_old.tm',
                    '--sites', 'candidate239/sites_logical.json', '--states', '239',
                    '--output', 'candidate239/universal_runtime.json'],
                 'candidate239/universal_runtime.json', 2247513),
            ]
            for label, command, path, count in jobs:
                run(label, command)
                value = json.loads((work / path).read_text())
                require(value['status'] == 'UNIVERSAL_MATHEMATICAL_PASS' and
                        value['cases'] == 8386 and value['symbolic_steps'] == count and
                        value['minimum_actual_steps'] == 13,
                        f'{label}: unexpected universal result.')

        record = {'status': 'PASS', 'mode': 'full' if args.full else 'quick',
                  'manifest_files_verified': checked, 'checks': results,
                  'seconds': round(time.monotonic() - started, 3),
                  'canonical_machine_sha256': digest(work / 'candidate239/zfc_boundary239.tm'),
                  'scope': ('Executable certificate replay and ordinary proof evidence. '
                            'This driver does not invoke a Lean or Rocq kernel.'),
                  'work_directory_retained': str(work) if args.keep_work else None}
        if args.record:
            args.record.parent.mkdir(parents=True, exist_ok=True)
            args.record.write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps(record, indent=2))
    finally:
        if temporary is not None:
            temporary.cleanup()


if __name__ == '__main__':
    main()
