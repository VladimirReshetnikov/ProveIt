#!/usr/bin/env python3
"""Rebuild and check the release; --full reruns independent symbolic checks.

Python 3.10+, standard library only, no network. Keep assertions enabled.
Fresh verification outputs go to a temporary directory, not into the release.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
FAMILIES = ('PA194F', 'PA194A', 'PA194X', 'PA194R')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def manifest():
    path = ROOT / 'SHA256SUMS'
    if not path.exists():
        print('Manifest not present in development tree; no manifest check performed.', flush=True)
        return 0
    count = 0
    for line in path.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        item = ROOT / relative
        require(item.is_file(), 'Missing manifest file: ' + relative)
        require(hashlib.sha256(item.read_bytes()).hexdigest() == expected,
                'Manifest mismatch: ' + relative)
        count += 1
    print(f'PASS: {count} manifest entries.', flush=True)
    return count


def run(label, arguments):
    print(label + ' ...', flush=True)
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    result = subprocess.run([sys.executable, *map(str, arguments)], cwd=ROOT,
                            env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout, flush=True)
        raise RuntimeError(f'{label}: exit {result.returncode}')
    print('PASS: ' + label, flush=True)
    return result.stdout


def compare_outputs(directory, label):
    for family in FAMILIES:
        expected, actual = ROOT / 'machines' / family, directory / family
        for name in ('machine.native.tm', 'machine.tm'):
            require((expected / name).read_bytes() == (actual / name).read_bytes(),
                    f'{label}: {family}/{name} bytes differ')
        for name in ('labels.json', 'sites.json', 'instructions.json'):
            require(json.loads((expected / name).read_text()) ==
                    json.loads((actual / name).read_text()),
                    f'{label}: {family}/{name} objects differ')
    print(f'PASS: {label}: all four tables, source graphs, paths and label maps agree.',
          flush=True)


def main():
    if not __debug__:
        raise SystemExit('Do not use -O or PYTHONOPTIMIZE: assertions must remain enabled.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true',
                    help='Rerun all four independent literal checks (several minutes).')
    ap.add_argument('--skip-manifest', action='store_true',
                    help='For deliberate local development only: skip release checksums.')
    args = ap.parse_args()
    began = time.monotonic()
    if not args.skip_manifest:
        manifest()
    with tempfile.TemporaryDirectory(prefix='pa194-verify-') as work:
        work = Path(work)
        construction = work / 'construction'
        run('Rebuilding F/A/X with every construction contract',
            ['construction/build.py', '--family', 'all', '--output', construction])
        run('Rebuilding R with every construction contract',
            ['construction/build_reassociated.py', '--output', construction / 'PA194R'])
        compare_outputs(construction, 'Fresh construction versus release')
        run('Checking all three small zero cuts', ['proofs/check_zero_cuts.py'])
        run('Independent four-site proof premises',
            ['verification/four_site_cut.py', 'inputs/pa194CS.instructions.json',
             'machines/PA194F/instructions.json'])
        compare_outputs(ROOT / 'verification/recorded', 'Recorded independent outputs versus release')
        run('Checking recorded contract and startup bindings',
            ['verification/compare_recorded.py', '--output', work / 'recorded_comparison.json'])
        rejection = work / 'rejected103'
        rejection.mkdir()
        for name in ('replay.py', 'machine.native.tm', 'trace.json'):
            (rejection / name).write_bytes((ROOT / 'research/rejected103' / name).read_bytes())
        run('Replaying rejected startup (halt at 1361)', [rejection / 'replay.py'])
        for family in FAMILIES:
            novelty = json.loads(run('Checking corpus novelty of ' + family,
                ['comparison/compare_candidate.py', ROOT / 'machines' / family / 'machine.tm']))
            require(novelty['novel_up_to_state_renaming_root_choice_reflection_and_global_bit_complement'],
                    family + ' matches an existing reference graph')
        if args.full:
            independent = work / 'independent'
            run('Independent literal F: all 4746 outcomes',
                ['verification/check_literal.py', '--output', independent])
            run('Independent literal A/X: all 4746 outcomes each',
                ['verification/check_companions.py', '--family', 'both', '--output', independent])
            run('Independent literal R: all 4746 outcomes',
                ['verification/check_reassociated.py', '--output', independent])
            compare_outputs(independent, 'Fresh independent outputs versus release')
        else:
            print('Independent universal checks were validated from recorded outputs; '
                  'use --full to rerun the symbolic engines.', flush=True)
    print(json.dumps({'status': 'PASS', 'machines': list(FAMILIES),
                      'independent_symbolic_checks_rerun': args.full,
                      'kernel_proof': False,
                      'elapsed_seconds': round(time.monotonic() - began, 3)}, indent=2))


if __name__ == '__main__':
    main()
