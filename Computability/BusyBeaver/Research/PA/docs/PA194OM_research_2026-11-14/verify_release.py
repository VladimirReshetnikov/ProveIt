#!/usr/bin/env python3
"""Offline reconstruction and finite-certificate replay for PA194OM/OMF.

Python 3.10+, standard library only, assertions enabled. No network calls.
Default: regenerate both oracle-free physical certificates. --quick retains
those certificates and explicitly reports that the physical replay was skipped.
Neither mode checks the entire inherited written PA calibration in a kernel.
"""
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

ROOT = Path(__file__).resolve().parent
NAMES = ('PA194OM', 'PA194OMF')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path, help='Optional final JSON receipt')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Python assertions must be enabled; do not use -O.')
    manifest = ROOT / 'MANIFEST.sha256.json'
    if manifest.exists():
        entries = json.loads(manifest.read_text())
        for name, digest in entries.items():
            assert sha(ROOT / name) == digest, f'Archive digest mismatch: {name}'
        print(f'Archive digest check: {len(entries)} files.', flush=True)
    else:
        entries = {}
        print('Development run: final archive manifest is not present.', flush=True)
    started = time.monotonic()
    stages = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')

    def run(label, script, *arguments):
        print(label + ' ...', flush=True)
        t = time.monotonic()
        result = subprocess.run([sys.executable, '-B', str(ROOT / script),
                                 *map(str, arguments)], cwd=ROOT, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True)
        if result.returncode:
            print(result.stdout)
            raise RuntimeError(f'{label} failed with exit code {result.returncode}')
        stages.append(dict(name=label, status='PASS',
                           seconds=round(time.monotonic()-t, 3),
                           stdout=result.stdout))
        print(label + ': PASS', flush=True)

    with tempfile.TemporaryDirectory(prefix='pa194-om-replay-') as temp:
        work = Path(temp)
        rebuilt = work / 'machines'
        run('Deterministic table reconstruction', 'construction/build.py',
            '--output', rebuilt)
        for name in NAMES:
            for filename in ('machine.tm', 'machine.native.tm', 'raw.native.tm',
                             'labels.json', 'nodes.json', 'grammar.json',
                             'sites.json', 'instructions.json', 'folds.json',
                             'local_folds.json', 'receipt.json'):
                assert (rebuilt/name/filename).read_bytes() == (
                    ROOT/'machines'/name/filename).read_bytes(), (name, filename)
            assert (ROOT/'comparison/new_machines'/f'{name}.tm').read_bytes() == (
                rebuilt/name/'machine.tm').read_bytes(), 'Novelty copy mismatch'
        if args.quick:
            for name in NAMES:
                shutil.copytree(ROOT/'machines'/name/'independent',
                                rebuilt/name/'independent')
            print('Quick mode: using retained physical contracts; no fresh physical replay.',
                  flush=True)
        else:
            run('Independent physical contracts for both new tables',
                'verification/check_physical.py', *(rebuilt/n for n in NAMES))
            for name in NAMES:
                for filename in ('contracts.json', 'list_lemmas.json', 'receipt.json'):
                    assert (rebuilt/name/'independent'/filename).read_bytes() == (
                        ROOT/'machines'/name/'independent'/filename).read_bytes(), (
                            name, filename, 'Fresh certificate mismatch')
        run('Relative proof, full startup and affine-clock bindings',
            'proof/check_relative_om.py', '--parent', ROOT/'references/AX11H',
            '--om', rebuilt/'PA194OM', '--omf', rebuilt/'PA194OMF',
            '--out', work/'relative.json')
        assert json.loads((work/'relative.json').read_text()) == json.loads(
            (ROOT/'proof/relative_om_inspection.json').read_text())
        run('Novelty against all 550 prior 194-state graphs',
            'comparison/verify_novelty.py', *(rebuilt/n/'machine.tm' for n in NAMES),
            '--output', work/'novelty.json')
        run('Exact all-start/allocation obstruction',
            'research/runtime193/allocation_all_starts.py')
        run('Replay of all 198 entire startup-hit tapes',
            'research/runtime193/replay_startup_hits.py')
        run('Replay of all 163 repair-validation records',
            'research/runtime193/verify_candidate_hits.py')
        run('Replay of 198 concrete source counterchecks',
            'research/runtime193/verify_counterchecks.py')
        # This research checker writes a deterministic receipt. Work on a copy.
        shutil.copytree(ROOT/'research/gate_x', work/'research/gate_x')
        shutil.copytree(ROOT/'research/ax11h_audit', work/'research/ax11h_audit')
        run('Independent arbitrary-consequent gate source binding',
            work/'research/gate_x/check_gate_x.py')
        assert (work/'research/gate_x/source_binding_receipt.json').read_bytes() == (
            ROOT/'research/gate_x/source_binding_receipt.json').read_bytes()

    receipt = dict(status='PASS', mode='quick' if args.quick else 'full',
                   physical_contracts_freshly_replayed=not args.quick,
                   checked_manifest_entries=len(entries),
                   machines={n: sha(ROOT/'machines'/n/'machine.tm') for n in NAMES},
                   total_seconds=round(time.monotonic()-started, 3), stages=stages,
                   scope='Finite reconstruction and certificate replay. Written relative iPRA '
                         'proof and inherited written AX11H arithmetic calibration remain '
                         'mathematical dependencies. No end-to-end Lean theorem or general '
                         '193-state lower bound is claimed.')
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'stages'}, indent=2))


if __name__ == '__main__':
    main()
