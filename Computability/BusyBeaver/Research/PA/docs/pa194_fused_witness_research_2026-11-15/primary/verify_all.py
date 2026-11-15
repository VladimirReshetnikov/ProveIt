#!/usr/bin/env python3
"""Reconstruct PA194FW and independently replay every delivered obligation.

Python 3.10+ and its standard library suffice. No network, external repository,
Lean installation, construction-side symbolic oracle, or optimized asserts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without -O or PYTHONOPTIMIZE.')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work', type=Path, default=ROOT / 'replay')
    a = p.parse_args()
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    logdir = work / 'logs'
    logdir.mkdir(exist_ok=True)
    receipt = {'family': 'PA194FW', 'status': 'RUNNING', 'checks': []}

    def run(name, script, *args):
        print(name, flush=True)
        command = [sys.executable, '-B', str(ROOT / script)] + [str(x) for x in args]
        result = subprocess.run(command, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        (logdir / (name + '.txt')).write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-12000:])
            raise SystemExit(f'{name} failed with status {result.returncode}')
        receipt['checks'].append({'name': name, 'status': 'PASS'})

    manifest = ROOT / 'SHA256SUMS.json'
    if manifest.exists():
        hashes = json.loads(manifest.read_text())
        for name, expected in hashes.items():
            assert sha(ROOT / name) == expected, ('manifest mismatch', name)
        receipt['manifest_entries'] = len(hashes)

    target = work / 'PA194FW'
    run('construction', 'construction/build.py', '--out', target, '--quick')
    reference = ROOT / 'machines/PA194FW'
    same = ('machine.tm', 'machine.native.tm', 'raw.native.tm',
            'fixedfold.native.tm', 'labels.json', 'nodes.json',
            'grammar.json', 'grammar.tree.json', 'fixedfold.json', 'folds.json',
            'fixedfold_cases.json', 'fold_cases.json', 'sites.json',
            'instructions.json')
    for name in same:
        assert (target / name).read_bytes() == (reference / name).read_bytes(), name
    receipt['reconstructed_identical_files'] = list(same)
    # The quick construction omits a redundant, oracle-based runtime pass.
    # This literal replay below is mandatory and reconstructs all four list
    # lemmas directly from rows before checking all 4809 complete tape outcomes.
    run('literal', 'verification/check_literal.py', target,
        '--output', work / 'literal')
    shutil.copytree(work / 'literal/PA194FW', target / 'independent',
                    dirs_exist_ok=True)
    run('source', 'verification/source/check_source_commands.py',
        '--machine', target, '--output', target / 'source_verification')
    run('fusion', 'verification/check_fusion_certificates.py',
        '--output', target / 'fusion_certificates.json')
    run('independent_fusion', 'verification/independent_fusion_audit.py',
        target / 'fusion_certificates.json', '--output',
        target / 'independent_fusion_audit.json')
    run('commands', 'verification/check_command_algebra.py',
        '--output', target / 'command_algebra.json')
    run('physical', 'verification/physical_ipra_audit.py',
        '--machine', target, '--output', target / 'physical_ipra_audit.json')
    for name in ('independent/contracts.json', 'independent/list_lemmas.json',
                 'independent/startup.json', 'independent/receipt.json',
                 'source_verification/receipt.json',
                 'fusion_certificates.json', 'command_algebra.json'):
        assert (target / name).read_bytes() == (reference / name).read_bytes(), name
    receipt.update(status='PASS', working_states=194, transitions=388,
                   source_sites=3695, source_outcomes=4809,
                   dense_sha256=sha(target / 'machine.tm'),
                   native_sha256=sha(target / 'machine.native.tm'),
                   kernel_proof=False,
                   scope='Complete finite reconstruction/source binding and '
                         'symbolic literal replay; not an end-to-end Lean proof.')
    (work / 'verification_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main()
