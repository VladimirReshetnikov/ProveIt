#!/usr/bin/env python3
"""Audit packet hashes and finite regressions; not a kernel or machine proof."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--work-dir', type=Path)
    args = parser.parse_args()
    require(__debug__, 'Run without Python -O: component checks use assertions.')
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for relative, item in manifest['files'].items():
        path = ROOT / relative
        require(path.is_file(), 'Missing file: ' + relative)
        content = path.read_bytes()
        require(len(content) == item['bytes'], 'Byte-count mismatch: ' + relative)
        require(hashlib.sha256(content).hexdigest() == item['sha256'],
                'SHA-256 mismatch: ' + relative)
    print(f"PASS: {len(manifest['files'])} file identities.", flush=True)
    identity = json.loads((ROOT / 'physical_research/evidence/quotient_price_identity/result.json').read_text())
    lowered = json.loads((ROOT / 'physical_research/evidence/quotient_price_lowered_v00/result.json').read_text())
    require(identity['states'] == 215 and identity['literal_identity_control'],
            'Invalid inherited-table identity control.')
    require(identity['table_sha256'] == '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2',
            'Wrong accepted native machine.')
    require(lowered['states'] == 234 and lowered['internal_prefixes'] == 4752
            and lowered['leaf_entries'] == 4753, 'Unexpected conservative allocation price.')
    calibration = json.loads((ROOT / 'quotient/verification/summary.json').read_text())
    require(calibration['status'] == 'pass' and calibration['total_modules'] == 110
            and calibration['all_modules_compiled_fresh']
            and calibration['cached_project_oleans_reused'] == 0,
            'Unexpected quotient proof build scope.')
    source_pins = json.loads((ROOT / 'quotient/quotient_source_hashes.json').read_text())
    for module, expected in source_pins.items():
        p = ROOT / 'quotient/lean' / (module.replace('.', '/') + '.lean')
        require(hashlib.sha256(p.read_bytes()).hexdigest() == expected,
                'Quotient proof source binding failed: ' + module)
    proof = json.loads((ROOT / 'proof_simplification/verification/kernel_receipt.json').read_text())
    require(len(proof['records']) == 13, 'Unexpected implication proof build scope.')
    for record in proof['records']:
        p = ROOT / 'proof_simplification/formal' / (record['module'].replace('.', '/') + '.lean')
        require(record['exit_code'] == 0 and hashlib.sha256(p.read_bytes()).hexdigest() == record['source_sha256'],
                'Implication proof source binding failed: ' + record['module'])
    print('PASS: exact source bindings for recorded 110-module and 13-module proof builds.', flush=True)
    if args.manifest_only:
        print('PASS: integrity and key machine-count receipts. No fresh proof-assistant run.')
        return 0
    if args.work_dir:
        work = args.work_dir.resolve()
        require(not work.exists() or not any(work.iterdir()), '--work-dir must be empty.')
        work.mkdir(parents=True, exist_ok=True)
    else:
        work = Path(tempfile.mkdtemp(prefix='proveit-k215-audit-'))
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    def check(label, command, cwd=ROOT):
        p = subprocess.run(command, cwd=cwd, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (work / (label + '.log')).write_text(p.stdout)
        require(p.returncode == 0, f'{label} failed; see {work / (label + ".log")}')
        print('PASS: ' + label, flush=True)
        return p.stdout
    semantic_script = ROOT / 'quotient/check_quotient_detachment.py'
    semantic = json.loads(check('finite-quotient-semantics', [sys.executable, str(semantic_script)]))
    require(semantic['tagged_guard_instances'] == 65536 and
            semantic['valid_extra_tag_instances'] == 3248 and
            semantic['compiler_guard_regressions'] == 8128,
            'Unexpected finite semantic coverage.')
    for source in ('v00', 'lowered_v00'):
        out = work / (source + '.json')
        check('complete-mp-' + source,
              [sys.executable, str(ROOT / 'physical_research/code/check_quotient_mp.py'),
               str(ROOT / 'physical_research/quotient/sources' / source / 'sites.json'),
               '--output', str(out)])
        receipt = json.loads(out.read_text())
        require(receipt['status'] == 'FINITE_FULL_MP_CONTRACT_PASS'
                and receipt['cases'] == 5688, 'Unexpected complete-MP finite coverage.')
    result = {'status': 'PASS', 'manifest_files': len(manifest['files']),
              'semantic_tagged_instances': semantic['tagged_guard_instances'],
              'compiler_guard_instances': semantic['compiler_guard_regressions'],
              'complete_mp_cases_per_source': 5688,
              'scope': 'Packet integrity and finite regression only. Kernel proofs and bounded searches have separate component drivers.'}
    (work / 'audit_result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS. Evidence: {work}')
    print('No new kernel check, binary acceptance proof, or state lower bound is inferred.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
