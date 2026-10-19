#!/usr/bin/env python3
"""Portable replay of the 239-state construction and accompanying research.

Default: exact construction, source extraction, local identities, startup,
and frontend transcription checks. --full also reruns both unbounded proofs.
All newly generated output goes to --output-dir, not the supplied evidence.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'verification'))
from verify_construction import verify


def load(path):
    return json.loads(path.read_text())


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--full', action='store_true')
    p.add_argument('--output-dir', type=Path, default=ROOT / 'replay')
    a = p.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Assertions must be enabled. Remove -O and PYTHONOPTIMIZE.')
    out = a.output_dir.resolve()
    assert out != ROOT and ROOT / 'evidence' not in [out, *out.parents], (
        'Choose an output directory separate from the delivered evidence.')
    out.mkdir(parents=True, exist_ok=True)
    (out / 'logs').mkdir(exist_ok=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    checks = []

    def run(name, script, *args):
        print('Checking', name, flush=True)
        result = subprocess.run([sys.executable, str(script), *map(str, args)],
                                cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / 'logs' / (name + '.log')).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'{name} failed; see {out / "logs" / (name + ".log")}')

    manifest = ROOT / 'SHA256SUMS'
    if manifest.exists():
        count = 0
        for line in manifest.read_text().splitlines():
            wanted, name = line.split('  ', 1)
            path = ROOT / name
            assert path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == wanted, (
                'Delivered payload changed', name)
            count += 1
        checks.append({'name': 'manifest', 'status': 'PASS', 'files': count})

    construction = verify()
    (out / 'construction.json').write_text(json.dumps(construction, indent=2) + '\n')
    checks.append({'name': 'construction', 'status': construction['status']})

    run('source_bridge', ROOT / 'verification/source_bridge/check_source_bridge.py',
        '--sites', ROOT / 'machines/sites_logical.json', '--output-dir', out / 'source_bridge')
    source = load(out / 'source_bridge/independent_source_bridge.json')
    assert source['status'] == 'PASS_INDEPENDENT_PINNED_SOURCE_DERIVATION'
    assert source['source_byte_equality'] and source['guarded_cases'] == 8386
    checks.append({'name': 'source_bridge', 'status': source['status']})

    run('local_fold', ROOT / 'verification/verify_guarded_fold239.py',
        '--old', ROOT / 'inputs/zfc240_old.tm', '--new', ROOT / 'machines/zfc239_old.tm',
        '--output-dir', out / 'local_fold')
    local = load(out / 'local_fold/guarded_fold239_certificate.json')
    assert local['status'] == 'PASS_EXACT_GUARDED_POSITIVE_BLOCK_CERTIFICATE'
    assert (out / 'local_fold/zfc239.tm').read_bytes() == (ROOT / 'machines/zfc239.tm').read_bytes()
    assert local['blank']['new_steps'] == 409835
    checks.append({'name': 'local_fold', 'status': local['status'],
                   'scope': 'Local identities and exact startup; full mode proves the additional runtime guard.'})

    run('sparse_dense_boot', ROOT / 'verification/check_boot239.py',
        ROOT / 'machines/zfc239_old.tm', '--output', out / 'boot.json')
    boot = load(out / 'boot.json')
    assert boot['status'] == 'EXACT_SPARSE_DENSE_BOOT_PASS' and boot['steps'] == 409835
    assert boot['logical_registers'] == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    checks.append({'name': 'sparse_dense_boot', 'status': boot['status']})

    # A separate finite-footprint implementation uses symbolic unknown cells.
    independent = out / 'independent_local'
    independent.mkdir(exist_ok=True)
    for name in ['check_local_blocks_239.py', 'baseline240.tm', 'helper91_target106_239.tm']:
        shutil.copy2(ROOT / 'research/source_compression' / name, independent / name)
    run('independent_local', independent / 'check_local_blocks_239.py')
    independent_result = load(independent / 'local_blocks_239_independent.json')
    assert independent_result['status'] == 'PASS_LITERAL_OPEN_TAPE_BLOCKS_AND_INCOMING_FACTS'
    checks.append({'name': 'independent_local', 'status': independent_result['status']})

    # Some research tools intentionally write beside themselves. Replay copies
    # them into the output directory to preserve all delivered evidence bytes.
    foundation = out / 'foundations'
    foundation.mkdir(exist_ok=True)
    for script in (ROOT / 'foundations').glob('*.py'):
        shutil.copy2(script, foundation / script.name)
    run('equational_packets', foundation / 'fuse_stack_packet.py', '--out', foundation / 'generated')
    for path in (ROOT / 'foundations/generated').iterdir():
        if path.suffix in ('.bits', '.equations') or path.name.startswith('stack_') and path.suffix == '.json':
            assert (foundation / 'generated' / path.name).read_bytes() == path.read_bytes(), path.name
    report = load(foundation / 'generated/verification.json')
    assert len(report['variants']) == 10
    run('shared_semantics', foundation / 'verify_shared_semantics.py')
    run('ground_rewrite_fixtures', foundation / 'check_ground_rewrite.py')
    assert load(foundation / 'ground_rewrite_checks.json')['status'] == 'PASS'
    checks.append({'name': 'equational_frontend', 'status': 'PASS',
                   'scope': 'Exact packet regeneration and bounded transcription fixtures; no consistency decision.'})

    if a.full:
        run('unbounded_runtime239', ROOT / 'verification/symbolic_runtime.py',
            '--table', ROOT / 'machines/zfc239_old.tm',
            '--sites', ROOT / 'machines/sites_logical.json',
            '--output', out / 'runtime239.json')
        runtime = load(out / 'runtime239.json')
        assert runtime['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
        assert (runtime['cases'], runtime['symbolic_steps'], len(runtime['directly_used_rows'])) == (8386, 2330575, 478)
        assert runtime['minimum_actual_steps'] == 13
        cases = load(out / 'runtime239_cases.json')
        assert cases == load(ROOT / 'evidence/candidate239_target106_universal_cases.json')
        checks.append({'name': 'unbounded_runtime239', 'status': runtime['status'], 'cases': 8386})

        run('unbounded_guard169', ROOT / 'verification/certify_guard169.py',
            '--table', ROOT / 'inputs/zfc240_old.tm',
            '--sites', ROOT / 'machines/sites_logical.json',
            '--output-dir', out / 'guard169')
        guard = load(out / 'guard169/guard169_universal.json')
        assert guard['status'] == 'PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD'
        assert (guard['cases'], guard['symbolic_rules'], guard['all_runtime_rows']) == (8386, 2322575, 480)
        assert guard['next_one_guard_visits'] == 32
        assert guard['minimum_certified_one_run_length_constant'] == 21
        assert load(out / 'guard169/guard169_visits.json') == load(ROOT / 'evidence/guard169_visits.json')
        checks.append({'name': 'unbounded_guard169', 'status': guard['status'], 'cases': 8386})

    summary = {
        'status': 'FULL_ORDINARY_CERTIFICATE_REPLAY_PASS' if a.full else 'QUICK_REPLAY_PASS',
        'full_unbounded_proofs_replayed': a.full,
        'checks': checks,
        'proof_status': 'Ordinary mathematical certificates; not a Lean/Rocq kernel theorem.',
        'consistency_status': 'No unconditional nonhalting or consistency claim.'
    }
    (out / 'replay_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
