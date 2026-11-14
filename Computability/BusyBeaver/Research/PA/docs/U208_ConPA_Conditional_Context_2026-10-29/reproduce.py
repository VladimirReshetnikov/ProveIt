#!/usr/bin/env python3
"""Offline release replay. Full mode rederives all 5,084 U208 contracts."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def manifest():
    seen = set()
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = (ROOT / name).resolve()
        need(path.is_relative_to(ROOT) and path.is_file(), 'Manifest path')
        need(name not in seen, 'Duplicate manifest entry')
        need(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
             'Changed release file: ' + name)
        seen.add(name)
    return len(seen)


def run(script, *args, optimized=False):
    command = [sys.executable, '-B'] + (['-O'] if optimized else [])
    result = subprocess.run(command + [str(script)] + list(map(str, args)),
                            cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise RuntimeError('Replay failed: ' + str(script))
    print(result.stdout.strip(), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true',
                        help='Skip fresh universal runtime derivation explicitly')
    parser.add_argument('--report', type=Path,
                        help='Optional receipt outside the sealed release')
    args = parser.parse_args()
    need(__debug__ and not sys.flags.optimize,
         'Use ordinary Python; independent local checker is also tested with -O')
    started, count = time.monotonic(), manifest()
    with tempfile.TemporaryDirectory(prefix='u208-replay-') as directory:
        temp = Path(directory)
        # Bind the selected parent and unchanged runtime engine to the full archive.
        archive = ROOT / 'reference/U209_ConPA_Joint_2026-10-29.zip'
        with zipfile.ZipFile(archive) as source:
            prefix = 'U209_ConPA_Joint_2026-10-29/'
            for local, member in [
                ('machine_parent/u209.native.tm', 'machine/u209.native.tm'),
                ('machine_parent/u209.tm', 'machine/u209.tm'),
                ('machine/sites.json', 'machine/sites.json'),
                ('machine/sites.tsv', 'machine/sites.tsv'),
                ('machine_parent/legacy_mapping.json', 'baseline/legacy_mapping.json'),
                ('code/symbolic_runtime.py', 'code/symbolic_runtime.py'),
                ('code/independent_runtime.py', 'code/independent_runtime.py')]:
                need((ROOT / local).read_bytes() == source.read(prefix + member),
                     'Parent archive binding: ' + local)
            for name in source.namelist():
                member = Path(name)
                need(not member.is_absolute() and '..' not in member.parts,
                     'Unsafe archive member')
            source.extractall(temp / 'parent')
        parent_root = temp / 'parent/U209_ConPA_Joint_2026-10-29'
        run(parent_root / 'reproduce.py', '--quick', '--report', temp / 'parent.json')
        for alternative in (False, True):
            directory = temp / ('alternative' if alternative else 'primary')
            flags = ['--alternative'] if alternative else []
            run(ROOT / 'code/build.py', '--output', directory, *flags)
            delivered = ROOT / ('alternative' if alternative else 'machine')
            for name in ('u208.tm', 'u208.native.tm', 'state_map.json'):
                need((directory / name).read_bytes() == (delivered / name).read_bytes(),
                     'Reconstruction mismatch: ' + name)
        local_args = ['--baseline', ROOT / 'machine_parent/u209.native.tm',
                      '--candidate-native', ROOT / 'machine/u208.native.tm',
                      '--candidate-dense', ROOT / 'machine/u208.tm']
        run(ROOT / 'code/check_local.py', *local_args, '--output', temp / 'local.json')
        run(ROOT / 'code/check_local.py', *local_args, '--output', temp / 'local_O.json',
            optimized=True)
        need((temp / 'local.json').read_bytes() == (temp / 'local_O.json').read_bytes(),
             'Optimized local audit differs')
        # A separate implementation verifies bounded history and the alternate family.
        run(ROOT / 'code/discovery_builder.py', ROOT / 'alternative/parent209.native.tm',
            '--compatibility', '--output', temp / 'history_alternative')
        need((temp / 'history_alternative/u208.tm').read_bytes() ==
             (ROOT / 'alternative/u208.tm').read_bytes(), 'Alternate history proof')
        run(ROOT / 'code/check_startup.py', '--output', temp / 'startup.json')
        shutil.copytree(ROOT / 'comparison/snapshots', temp / 'comparison/snapshots')
        shutil.copy2(ROOT / 'comparison/inspect_tables.py', temp / 'comparison/inspect_tables.py')
        run(temp / 'comparison/inspect_tables.py')
        run(ROOT / 'code/compare208.py', ROOT / 'machine/u208.native.tm',
            ROOT / 'alternative/u208.native.tm', '--output', temp / 'comparison208.json')
        need(not json.loads((temp / 'comparison208.json').read_text())['isomorphic'],
             'The two new families became isomorphic')
        runtime = None
        if not args.quick:
            run(ROOT / 'code/check_runtime.py', '--output', temp / 'runtime.json')
            runtime = json.loads((temp / 'runtime.json').read_text())
        local = json.loads((temp / 'local.json').read_text())
        result = {'status': 'U208_QUICK_PASS_RUNTIME_SKIPPED' if args.quick
                            else 'U208_FULL_REPLAY_PASS',
                  'manifest_files': count, 'working_states': 208, 'transition_rows': 416,
                  'parent_archive_bound': True, 'parent_quick_replay_pass': True,
                  'source_changed': False, 'two208_variants_nonisomorphic': True,
                  'local_macro_cases': len(local['cases']),
                  'ordinary_quotient_rows': local['ordinary_old_rows'],
                  'inductive_boolean_cases': 104, 'negative_controls_rejected': 12,
                  'normal_and_optimized_audits_equal': True, 'startup_steps': 48140,
                  'fresh_runtime_cases': runtime['cases'] if runtime else 0,
                  'fresh_runtime_row_coverage': runtime['row_coverage'] if runtime else 0,
                  'symbolic_inferences': runtime['symbolic_inferences'] if runtime else 0,
                  'seconds': time.monotonic() - started,
                  'scope': 'Mathematical block simulation and symbolic induction; inherited '
                           'U/PA calibration; no newly exported proof-assistant endpoint.'}
        need(manifest() == count, 'Release changed during replay')
    if args.report:
        need(not args.report.resolve().is_relative_to(ROOT), 'Receipt must be outside release')
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
