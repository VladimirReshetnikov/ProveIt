#!/usr/bin/env python3
"""Reproduce the K228 construction and mathematical certificates, offline.

Python 3.10+ standard library. Full unbounded symbolic checking is the default.
--quick stops after the source/fold construction and exact blank startup.
Outputs go to reproduced/ by default; delivered evidence is left intact.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run(script, *arguments):
    subprocess.run([sys.executable, '-B', str(ROOT / 'verification' / script),
                    *map(str, arguments)], check=True)


def main():
    require(__debug__ and not sys.flags.optimize, 'Assertions must be enabled: remove -O/-OO.')
    require(sys.version_info >= (3, 10), 'Python 3.10 or newer is required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'reproduced')
    parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    destination = args.output.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    upstream = ROOT / 'upstream/k230'
    h = destination / 'h'
    runtime = destination / 'runtime'
    run('build_h229.py', '--table', upstream / 'machine/k230.tm',
        '--sites', upstream / 'machine/sites230.json', '--output', h)
    require((h / 'sites_logical.json').read_bytes() ==
            (ROOT / 'source/sites_logical.json').read_bytes(),
            'Delivered source is not exactly reconstructed from the released K230 source.')
    sys.path.insert(0, str(ROOT / 'verification'))
    import table_reconstruction as reconstruction
    h_table, h_start = reconstruction.parse((h / 'k229_h_oldlabels.tm').read_bytes())
    require(h_start == 0, 'Unexpected H start state.')
    normalized_h = {(reconstruction.normalize(q), b):
                    (w, d, reconstruction.normalize(z))
                    for (q, b), (w, d, z) in h_table.items()}
    h_normalized_path = h / 'k229_h_normalized.tm'
    h_normalized_path.write_bytes(reconstruction.encode(normalized_h, 95))
    run('check_local_delayed.py', '--old', h_normalized_path,
        '--new', ROOT / 'machine/k228_normalized.tm',
        '--output', destination / 'delayed_local_conditional.json')
    run('check_boot_delayed.py', '--old', h_normalized_path,
        '--new', ROOT / 'machine/k228_normalized.tm', '--old-steps', 409691,
        '--output', destination / 'delayed_startup.json')
    arguments = ['--original', upstream / 'machine/k230.tm',
                 '--h-table', h / 'k229_h_oldlabels.tm',
                 '--sites', h / 'sites_logical.json',
                 '--machine', ROOT / 'machine/k228.tm',
                 '--engine-dir', ROOT / 'verification/kernels',
                 '--output-dir', runtime]
    if args.quick:
        arguments.append('--quick')
    run('verify_k228.py', *arguments)
    audit = ROOT / 'verification/audit_transfer.py'
    if audit.is_file():
        arguments = ['--package-root', ROOT, '--output-dir', destination / 'audit']
        if not args.quick:
            arguments += ['--runtime-dir', runtime]
        run('audit_transfer.py', *arguments)
    receipt = json.loads((runtime / 'verification.json').read_text())
    require(receipt['status'] == ('STATIC_CONSTRUCTION_AND_DENSE_STARTUP_PASS' if args.quick
                                 else 'K228_UNIVERSAL_MATHEMATICAL_PASS'),
            'The requested verification did not finish.')
    summary = {
        'status': 'QUICK_CONSTRUCTION_AND_STARTUP_PASS' if args.quick else 'K228_FULL_REPLAY_PASS',
        'canonical_machine_sha256': hashlib.sha256((ROOT / 'machine/k228.tm').read_bytes()).hexdigest(),
        'working_states': 228,
        'transition_rows': 456,
        'full_symbolic_runtime_replayed': not args.quick,
        'guarded_cases': None if args.quick else receipt['cases'],
        'symbolic_rules': None if args.quick else receipt['symbolic_steps'],
        'mathematical_proof_scope': 'Ordinary proof with executable induction certificates, composed with pinned K230 calibration.',
        'new_Rocq_or_Lean_endpoint': False,
        'independent_transfer_audit_included': audit.is_file(),
    }
    (destination / 'REPLAY_SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
