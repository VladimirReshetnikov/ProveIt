#!/usr/bin/env python3
"""Run the portable, scoped checks; no new <196-state TM is claimed."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise SystemExit('Run with assertions enabled: do not use -O or -OO.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    manifest = HERE / 'SHA256SUMS.json'
    checked = None
    if manifest.exists():
        expected = json.loads(manifest.read_text())
        for name, digest in expected['files'].items():
            path = HERE / name
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise ValueError(('Manifest mismatch', name))
        checked = len(expected['files'])
    results = []
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env.pop('PYTHONOPTIMIZE', None)
    with tempfile.TemporaryDirectory(prefix='pa_tm_replay_') as td:
        temp = Path(td)
        jobs = [
            ('combined157', ['combined157/verify_combined157.py']),
            ('source_zero5', ['source_zero5/verify.py']),
            ('residual_source', ['residual_mp/residual_source.py', '--output', str(temp/'residual_source')]),
            ('residual_command_interfaces', ['residual_mp/check_residual_commands.py', '--output', str(temp/'residual_commands.json')]),
            ('comparison208', ['comparison208/compare_designs.py', '--output', str(temp/'comparison208.json')]),
            ('census196', ['verify_selected196.py']),
            ('synthetic_search_control', ['local_search/verify_control.py']),
            ('rejected_prefix', ['rejected_prefix/verify.py']),
        ]
        for name, command in jobs:
            start = time.monotonic()
            run = subprocess.run([sys.executable, *command], cwd=HERE, env=env,
                                 text=True, capture_output=True)
            if run.returncode:
                sys.stderr.write(run.stdout + run.stderr)
                raise SystemExit(f'{name} failed with exit code {run.returncode}')
            try:
                evidence = json.loads(run.stdout)
            except json.JSONDecodeError:
                evidence = {'stdout': run.stdout, 'stderr': run.stderr}
            results.append({'check': name, 'exit_code': run.returncode,
                            'seconds': round(time.monotonic()-start, 6),
                            'result': evidence})
            print(f'PASS {name}', file=sys.stderr, flush=True)
    receipt = {
        'status': 'ALL_SCOPED_QUICK_CHECKS_PASSED',
        'python': sys.version.split()[0],
        'manifest_files_verified': checked,
        'checks': results,
        'scope': 'Source identities, local source splice and finite command regressions, graph census, synthetic control and rejected-prefix replay. Not a new literal TM refinement, complete native-AX evaluation, Lean build, PA biconditional, or exhaustive-search replay.'
    }
    content = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        args.output.write_text(content)
    print(content, end='')


if __name__ == '__main__':
    main()
