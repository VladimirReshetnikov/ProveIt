#!/usr/bin/env python3
"""Replay the principal research checks from a self-contained extracted ZIP.

Python 3.10+ standard library. Run without -O. No network or proof assistant.
This verifies finite certificates and the explicitly stated symbolic rules;
the mathematical box lemmas and prior logical calibration remain as stated
in the report. It does not certify a machine below 252 states.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, tempfile, time

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'source/Computability/BusyBeaver/Research/ZFC'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='New or empty directory for fresh replay logs')
    parser.add_argument('--extended', action='store_true',
                        help='Also regenerate the pinned baseline and MP0 source relation, and replay 17,325 positive transfers')
    args = parser.parse_args()
    assert __debug__, 'Python -O disables required assertions.'
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-prefix-replay-'))
    if out.exists() and any(out.iterdir()):
        parser.error('--output must be new or empty')
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    records = []
    def run(label, arguments):
        started = time.monotonic()
        command = [sys.executable, '-B', *map(str, arguments)]
        completed = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (label + '.log')).write_text(completed.stdout)
        record = dict(check=label, returncode=completed.returncode,
                      elapsed_seconds=round(time.monotonic() - started, 4))
        records.append(record)
        print(('PASS' if completed.returncode == 0 else 'FAIL'), label, flush=True)
        if completed.returncode:
            print(completed.stdout)
            raise SystemExit(completed.returncode)
    run('prefix-table-startup-and-all-guards', ['bootstrap/verify_prefix_rebased.py'])
    run('independent-prefix-phase', ['logic_audit/audit_prefix_phase.py', '--output', out / 'prefix-phase.json'])
    run('mp-original-engine-startup', ['bootstrap/verify_mp_rebased.py'])
    run('mp-source-relation-independent', ['bootstrap/verify_mp_source_certificate.py', '--output', out / 'mp-source-relation.json'])
    run('source-rewrite-blocks', ['logic_audit/verify_source_rewrite.py', '--output', out / 'source-rewrites.json'])
    run('nip-register-contracts', ['logic_audit/verify_nip_specialization.py', '--output', out / 'nip.json'])
    run('projected-gen-source', ['logic_audit/verify_projected_gen.py', '--output', out / 'projected-gen.json'])
    run('rejected250-counterexample', ['redesign/shared_scanner_counterexample.py'])
    if args.extended:
        run('pinned252-baseline', [BASE / 'candidate252_independent_audit.py', '--repo', ROOT / 'source',
                                  '--source-table', BASE / 'candidate-permutation252/zfc_permutation252_old.tm',
                                  '--output', out / 'baseline.json'])
        run('regenerate-mp-source-relation', [BASE / 'mp_success_mapping.py', '--repo', ROOT / 'source',
                                             '--output', out / 'mp-source-mapping'])
        run('check-regenerated-mp-source-relation', ['bootstrap/verify_mp_source_certificate.py',
                                                    '--directory', out / 'mp-source-mapping',
                                                    '--output', out / 'regenerated-mp-source-check.json'])
        run('literal-positive-root-transfers', ['redesign/prefix_decrement.py'])
    expected = {
        'bootstrap/prefix_rebased252.tm': 'b91dc16e60c26780a3006072347c15ea058fa0fab6c0b4b5493967cab11c6234',
        'bootstrap/prefix_rebased252_canonical.tm': 'fd09cc6c76b04e1f3eb34c5d6fec5f14bd3ef564767aae70023bb988599f3bc7',
    }
    for relative, digest in expected.items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest
    summary = dict(status='all_requested_checks_passed', checks=records,
                   working_states=252, table_hashes=expected,
                   fresh_proof_assistant_build=False,
                   verified_below252=False,
                   scope='Exact finite executions and ordinary symbolic checks with the report\'s explicit mathematical and imported contracts.')
    (out / 'replay-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('All requested checks passed. Results:', out)
    print('State count remains 252; no fresh Lean/Coq endpoint is claimed.')

if __name__ == '__main__':
    main()
