#!/usr/bin/env python3
"""Replay the release's finite checks without modifying the release.

Python 3.10+; standard library only. Assertions must be enabled.
--literal repeats the longer independent arbitrary-register source checker.
--coverage also recomputes every catalog identity from every possible root.
These checks accompany the written iPRA proof; they are not a proof kernel.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
NAMES = ('PA194ORHF', 'PA194ORHBF')
EXPECTED = {
    'PA194ORHF': ('9818435880b25294c15c1f9852ecad44af53a8e185410eeeb6c0ec99a69de6a6', 57890),
    'PA194ORHBF': ('c8cdfc187b0155c0baa9e4d5c0141dad184ae95f1a712b22b64dc0e013c1e247', 57982),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


def run(script, *args, log=None, stream=False):
    cmd = [sys.executable, '-B', str(ROOT / script), *map(str, args)]
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    if stream:
        subprocess.run(cmd, cwd=ROOT, env=env, check=True)
    else:
        result = subprocess.run(cmd, cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if log is not None:
            log.write_text(result.stdout)
        require(result.returncode == 0, f'{script} failed:\n{result.stdout[-6000:]}')


def integrity():
    manifest = ROOT / 'SHA256SUMS'
    require(manifest.is_file(), 'The release SHA256SUMS file is missing.')
    count = 0
    for line in manifest.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        require(path.resolve().is_relative_to(ROOT), 'Invalid manifest path')
        require(path.is_file(), f'Missing release file: {relative}')
        require(sha(path) == expected, f'Hash mismatch: {relative}')
        count += 1
    require(count > 600, 'Incomplete release manifest')
    print(f'PASS: {count} frozen file hashes', flush=True)
    return count


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--literal', action='store_true')
    ap.add_argument('--coverage', action='store_true')
    args = ap.parse_args()
    require(__debug__, 'Assertions must be enabled; do not use python -O.')
    sys.dont_write_bytecode = True
    count = integrity()
    with tempfile.TemporaryDirectory(prefix='pa194_orhf_replay_') as d:
        temp = Path(d)
        out = temp / 'machines'
        run('construction/build.py', '--output', out, log=temp / 'build.log')
        parent = ROOT / 'reference/PA194ORH'
        for name in NAMES:
            frozen = ROOT / 'machines' / name
            rebuilt = out / name
            for filename in ('machine.tm', 'machine.native.tm', 'labels.json', 'receipt.json'):
                require((frozen / filename).read_bytes() == (rebuilt / filename).read_bytes(),
                        f'Reconstruction mismatch: {name}/{filename}')
            for filename in ('sites.json', 'instructions.json'):
                require(json.loads((frozen / filename).read_text()) ==
                        json.loads((parent / filename).read_text()),
                        f'Source metadata mismatch: {name}/{filename}')
                shutil.copyfile(frozen / filename, rebuilt / filename)
            receipt = json.loads((frozen / 'independent/receipt.json').read_text())
            expected_sha, boot = EXPECTED[name]
            require(sha(frozen / 'machine.tm') == expected_sha, 'Wrong dense table identity')
            require(receipt['dense_sha256'] == expected_sha and receipt['startup_steps'] == boot,
                    'Stored literal-check receipt belongs to another table')
            require(receipt['native_sha256'] == sha(frozen / 'machine.native.tm'),
                    'Stored native hash mismatch')
            require(receipt['contracts_sha256'] == sha(frozen / 'independent/contracts.json'),
                    'Stored contract hash mismatch')
            require(receipt['status'] == 'PASS' and receipt['source_outcomes'] == 4778,
                    'Incomplete stored literal-check receipt')
        print('PASS: exact reconstruction, source binding, and complete blank startups', flush=True)

        run('verification/verify_shortcuts.py',
            '--orh', parent / 'machine.native.tm',
            '--orhb', ROOT / 'reference/PA194ORHB/machine.native.tm',
            '--orhf', out / NAMES[0] / 'machine.native.tm',
            '--orhbf', out / NAMES[1] / 'machine.native.tm',
            '--output', temp / 'shortcuts.json', log=temp / 'shortcuts.log')
        selectors = module('orhb_certificate', ROOT / 'reference/build_orhb.py')
        result = selectors.check(selectors.read(parent / 'machine.native.tm'),
                                 selectors.read(ROOT / 'reference/PA194ORHB/machine.native.tm'))
        require(result['ordinary_cases'] == 384 and len(result['exceptional_cases']) == 4,
                'Incomplete B selector certificate')
        run('reference/build_orhb.py', '--output', temp / 'ORHB', log=temp / 'orhb.log')
        for filename in ('machine.tm', 'machine.native.tm', 'labels.json'):
            require((temp / 'ORHB' / filename).read_bytes() ==
                    (ROOT / 'reference/PA194ORHB' / filename).read_bytes(),
                    f'B-parent reconstruction mismatch: {filename}')
        print('PASS: both simultaneous-shortcut invariants and the B-selector transfer', flush=True)

        run('reference/ORH_proof/relative_ORH_check.py', '--output', temp / 'orh_binding.json',
            log=temp / 'orh_binding.log')
        binding = json.loads((temp / 'orh_binding.json').read_text())
        require(binding['status'] == 'PASS' and binding['source_instruction_arrays_identical']
                and binding['changed_source_addresses'] == 134,
                'Inherited AX11H-to-ORH finite binding failed')
        print('PASS: inherited AX11H-to-ORH source and clock certificate binding', flush=True)

        run('comparison/fast_novelty.py', '--corpus', ROOT / 'comparison/corpus194',
            '--candidate', out / NAMES[0] / 'machine.tm',
            '--candidate', out / NAMES[1] / 'machine.tm',
            '--out', temp / 'novelty.json', log=temp / 'novelty.log')
        novelty = json.loads((temp / 'novelty.json').read_text())
        require(novelty['194_loose_action_classes_among_minimal_graphs'] == 548,
                'Wrong novelty corpus size')
        require(len(novelty['nonminimal_194_byte_forms']) == 2, 'Missing diagnostic tables')
        require(all(c['novel'] and not c['matches'] for c in novelty['candidates']),
                'A candidate matched the retained corpus')
        require(all(not c['isomorphic_under_any_allowed_symmetry']
                    for c in novelty['mutual_comparison']), 'Candidates are equivalent graphs')
        print('PASS: both tables distinct from the 548 prior spanning graphs and two diagnostics', flush=True)

        if args.coverage:
            run('comparison/check_coverage.py', '--out', temp / 'coverage.json', stream=True)
            print('PASS: all 528 catalogued 194-state and 55 catalogued 193-state classes covered', flush=True)
        if args.literal:
            run('verification/check.py', out / NAMES[0], out / NAMES[1], stream=True)
            for name in NAMES:
                for filename in ('receipt.json', 'contracts.json', 'list_lemmas.json'):
                    require((out / name / 'independent' / filename).read_bytes() ==
                            (ROOT / 'machines' / name / 'independent' / filename).read_bytes(),
                            f'Independent literal replay differs: {name}/{filename}')
            print('PASS: full independent literal checks reproduced the frozen evidence', flush=True)
    print(json.dumps({'status': 'PASS', 'manifest_files': count, 'machines': list(NAMES),
                      'full_literal_replayed': args.literal, 'catalog_coverage_recomputed': args.coverage,
                      'scope': 'Finite certificates and table binding; written iPRA calibration is a separate mathematical dependency.'}, indent=2))


if __name__ == '__main__':
    main()
