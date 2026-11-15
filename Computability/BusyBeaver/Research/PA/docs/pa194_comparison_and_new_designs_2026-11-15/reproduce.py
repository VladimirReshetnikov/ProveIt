#!/usr/bin/env python3
"""Check the release and replay its constructions without changing frozen files."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--lc', action='store_true', help='Replay the inherited LC physical proof certificates.')
    parser.add_argument('--research', action='store_true', help='Also repeat bounded research experiments; requires C++17.')
    args = parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run with assertions enabled, without Python -O.')
    output = (args.output or Path(tempfile.mkdtemp(prefix='pa194-sf-verification-'))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = ROOT / 'MANIFEST.sha256'
    checked = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        file = ROOT / relative
        assert file.is_file(), relative
        assert hashlib.sha256(file.read_bytes()).hexdigest() == expected, relative
        checked += 1
    stages = []

    def run(label, script, *arguments):
        print('Checking ' + label, flush=True)
        result = subprocess.run([sys.executable, '-B', str(script), *map(str, arguments)],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (output / (label + '.log')).write_text(result.stdout)
        if result.returncode:
            print(result.stdout)
            raise RuntimeError(label + ' failed')
        stages.append({'stage': label, 'exit_code': 0})

    run('constructions_and_comparison', ROOT / 'verify_inventory_composites.py',
        '--output', output / 'core', *(['--lc'] if args.lc else []))
    run('late_catalog_reconciliation', ROOT / 'comparison/late_snapshot/verify.py',
        '--output', output / 'late_snapshot_receipt.json')
    if args.research:
        run('physical_searches', ROOT / 'research/physical/reproduce.py',
            '--output', output / 'physical')
        run('reversed_cantor', ROOT / 'research/theory/explore_reverse_cantor.py',
            '--output', output / 'reverse_cantor')
        with tempfile.TemporaryDirectory(prefix='pa194-closed-macro-') as temporary:
            work = Path(temporary) / 'closed_macro'
            shutil.copytree(ROOT / 'research/closed_macro', work,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            run('closed_macro_search', work / 'search.py', '--full')
            shutil.copy2(work / 'replay.json', output / 'closed_macro.json')
    result = {
        'status': 'PASS', 'manifest_files_checked': checked, 'stages': stages,
        'inherited_lc_replay_requested': args.lc,
        'additional_research_replay_requested': args.research,
        'kernel_checked': False,
        'absolute_calibration_status': 'Explicitly imported written AX11H theorem; not checked by this program.',
        'output_directory': str(output),
    }
    (output / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
