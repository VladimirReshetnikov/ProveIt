#!/usr/bin/env python3
"""Replay the 238-state construction in a fresh temporary copy.

Default: construction, source certificate/identity, independent local proof,
logical obstruction, and the complete unbounded final-table runtime proof.
--with-guard also repeats the separate unbounded boundary239 selector proof.
--quick omits both unbounded runs and labels its result partial.
No network access, third-party Python package, Lean or Rocq is required.
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


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--with-guard', action='store_true')
    ap.add_argument('--output', type=Path,
                    help='Retain fresh receipts in a new or empty directory')
    args = ap.parse_args()
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required')
    require(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),
            'Run with assertions enabled and PYTHONOPTIMIZE unset')
    require(not (args.quick and args.with_guard), '--quick and --with-guard are incompatible')
    manifest_count = 0
    manifest = ROOT / 'SHA256SUMS'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected, name = line.split('  ', 1)
            path = (ROOT / name).resolve()
            require(path.is_relative_to(ROOT), 'Manifest path escapes archive')
            require(path.is_file() and sha(path) == expected, 'Manifest mismatch: ' + name)
            manifest_count += 1
    if args.output:
        output = args.output.resolve()
        require(not output.exists() or not any(output.iterdir()), 'Output must be new or empty')
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = None
    records = []
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='zfc238-replay-') as temporary:
        work = Path(temporary) / 'bundle'
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        receipt_dir = Path(temporary) / 'receipts'
        receipt_dir.mkdir()
        env = os.environ.copy()
        env['PYTHONDONTWRITEBYTECODE'] = '1'

        def run(name, arguments, receipt, status):
            print('Checking ' + name + ' ...', flush=True)
            begin = time.monotonic()
            with (receipt_dir / (name + '.log')).open('w') as log:
                result = subprocess.run([sys.executable, '-B', *map(str, arguments)],
                                        cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                print((receipt_dir / (name + '.log')).read_text()[-6000:], file=sys.stderr)
            require(result.returncode == 0, name + ' returned a failure')
            data = json.loads(receipt.read_text())
            require(data.get('status') == status, name + ': unexpected status ' + str(data.get('status')))
            if receipt.parent != receipt_dir:
                shutil.copyfile(receipt, receipt_dir / (name + '.json'))
            records.append({'check': name, 'status': status,
                            'seconds': round(time.monotonic() - begin, 3), 'receipt_sha256': sha(receipt)})
            print('  ' + status, flush=True)
            return data

        v = work / 'vendor/boundary239'
        source = work / 'source/sites_logical.json'
        machine = work / 'machines/zfc238_old.tm'
        run('stored_evidence_consistency', [work / 'verification/check_evidence.py',
            '--output', receipt_dir / 'stored_evidence_consistency.json'],
            receipt_dir / 'stored_evidence_consistency.json',
            'PACKAGED_EVIDENCE_INTEGRITY_AND_CONSISTENCY_PASS')
        run('transition_appendix', [work / 'verification/render_transition_table.py', '--check'],
            receipt_dir / 'transition_appendix.log', 'EXACT_TRANSITION_APPENDIX_PASS')
        run('inherited_boundary_construction', [v / 'candidate239/build_candidate239.py'],
            v / 'candidate239/literal_checks.json', 'PASS')
        built = receipt_dir / 'constructed'
        data = run('construction_and_blank_prefix', [work / 'verification/build238.py', '--output', built],
                   built / 'construction.json', 'EXACT_238_CONSTRUCTION_PASS')
        require((built / 'zfc238.tm').read_bytes() == (work / 'machines/zfc238.tm').read_bytes(),
                'Canonical delivered table differs from reconstruction')
        require((built / 'zfc238_old.tm').read_bytes() == machine.read_bytes(),
                'Inherited delivered table differs from reconstruction')
        extra = v / 'formalism/extra'
        run('source_control_certificate', [extra / 'check_rotation_certificate.py',
            '--report', receipt_dir / 'source_control_certificate.json'],
            receipt_dir / 'source_control_certificate.json', 'PASS_EXACT_SOURCE_CONTROL_CERTIFICATE')
        require(source.read_bytes() == (extra / 'boundary224_sites.json').read_bytes(),
                'Runtime source differs from certified source')
        run('exact_source_and_seed_identity', [v / 'source_interface/check_source_interface.py',
            '--output', receipt_dir / 'exact_source_and_seed_identity.json'],
            receipt_dir / 'exact_source_and_seed_identity.json', 'EXACT_LEAN_SOURCE_DATA_AND_SEED_IDENTITY_PASS')
        run('independent_composition', [work / 'verification/check_composition.py',
            '--reference', v / 'boundary240/boundary240_old.tm',
            '--boundary239', v / 'candidate239/zfc_boundary239_old.tm',
            '--candidate238', machine, '--output', receipt_dir / 'independent_composition.json'],
            receipt_dir / 'independent_composition.json', 'INDEPENDENT_238_COMPOSITION_PASS')
        logic = work / 'research/formalisms'
        run('fourth_input_obstruction', [logic / 'check_fourth_input_no_go.py'],
            logic / 'fourth_input_no_go_certificate.json', 'PASS')
        # This auxiliary checker prints its JSON certificate directly.
        colored_receipt = receipt_dir / 'colored_gic_identities.json'
        with colored_receipt.open('w') as log:
            colored = subprocess.run([sys.executable, '-B', str(logic / 'check_colored_gic_identities.py')],
                                     cwd=work, env=env, stdout=log, stderr=subprocess.PIPE, text=True)
        require(colored.returncode == 0, 'Colored GIC finite identities failed: ' + colored.stderr)
        colored_data = json.loads(colored_receipt.read_text())
        require(colored_data.get('status') == 'PASS' and
                colored_data.get('GIC_two_point_cases') == 65536 and
                colored_data.get('meet_closure_pairs') == 256,
                'Unexpected colored GIC finite identity counts')
        records.append({'check': 'colored_gic_finite_identities', 'status': 'PASS',
                        'receipt_sha256': sha(colored_receipt)})
        association = work / 'research/source_association'
        run('source_associativity_criterion', [association / 'check_associativity.py'],
            association / 'associativity_certificate.json', 'LITERAL_LOCAL_CONTROL_SIGNATURES_PASS')
        run('shorter_source_exact_history', [association / 'check_source_result.py'],
            association / 'source_result_certificate.json', 'EXACT_SOURCE_CONTROL_GRAPH_PASS')
        if not args.quick:
            data = run('complete_238_runtime', [v / 'validation/check_literal_runtime.py',
                '--table', machine, '--sites', source, '--states', 238,
                '--output', receipt_dir / 'complete_238_runtime.json'],
                receipt_dir / 'complete_238_runtime.json', 'UNIVERSAL_MATHEMATICAL_PASS')
            require((data['cases'], data['symbolic_steps'], data['minimum_actual_steps']) ==
                    (8386, 2255513, 13), 'Unexpected final runtime proof counts')
            require(len(data['directly_used_rows']) == 476, 'Incomplete transition-row coverage')
            require(data['table_sha256'] == sha(machine), 'Runtime table identity differs')
        if args.with_guard:
            data = run('fresh_boundary239_guard', [work / 'verification/check_boundary_selector_guard.py',
                '--checker', work / 'vendor/guard239/symbolic_runtime.py',
                '--table', v / 'candidate239/zfc_boundary239_old.tm', '--sites', source,
                '--output', receipt_dir / 'fresh_boundary239_guard.json'],
                receipt_dir / 'fresh_boundary239_guard.json', 'FRESH_BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS')
            require(data['complete_cases'] == 8386 and data['minimum_right_one_run'] >= 2,
                    'Guard failed its required scope')
        result = {
            'status': ('QUICK_CHECKS_PASS_UNBOUNDED_REPLAY_OMITTED' if args.quick
                       else 'FULL_238_MATHEMATICAL_REPLAY_PASS'),
            'manifest_files_verified': manifest_count,
            'complete_238_runtime_replayed': not args.quick,
            'separate_selector_guard_replayed': args.with_guard,
            'canonical_sha256': sha(work / 'machines/zfc238.tm'),
            'checks': records, 'seconds': round(time.monotonic() - started, 3),
            'scope': 'Ordinary mathematical certificates and exact finite data. '
                     'Inherited source/calculus/theory calibration is cited; no Lean/Rocq kernel run '
                     'or internal PA derivation is performed by this driver.',
        }
        (receipt_dir / 'reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
        if output:
            shutil.copytree(receipt_dir, output, dirs_exist_ok=True)
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
