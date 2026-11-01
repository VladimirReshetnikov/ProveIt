#!/usr/bin/env python3
"""Re-run the frozen-source audit and driver controls on copied inputs."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

D = Path(__file__).resolve().parent
PROJECT = D.parent.parent / 'research/fresh-project-closure'
SNAPSHOT = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
EXPECTED_SNAPSHOT = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
FILES = ('prepare.py', 'rebuild.py', 'audit_snapshot.py', 'compare.py', 'run_pair.py', 'test_rebuild.py')

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    manifest = SNAPSHOT / 'manifest.json'
    assert sha(manifest) == EXPECTED_SNAPSHOT
    before = {name: sha(PROJECT / name) for name in FILES}
    saved = D / 'inputs'
    saved.mkdir(exist_ok=False)
    for name in FILES:
        shutil.copyfile(PROJECT / name, saved / name)
        assert sha(saved / name) == before[name]
    with tempfile.TemporaryDirectory(prefix='fresh-project-independent-audit-') as td:
        tmp = Path(td)
        result = subprocess.run([sys.executable, str(saved / 'test_rebuild.py')],
                                capture_output=True, text=True, timeout=300)
        assert result.returncode == 0, (result.stdout, result.stderr)
        source_receipt = tmp / 'source-audit.json'
        source = subprocess.run([sys.executable, str(saved / 'audit_snapshot.py'), str(SNAPSHOT),
                                 '--output', str(source_receipt)],
                                capture_output=True, text=True, timeout=180)
        assert source.returncode == 0, (source.stdout, source.stderr)
        source_data = json.loads(source_receipt.read_text())
        assert source_data['status'] == 'PASS_SOURCE_SNAPSHOT_AUDIT'
        assert source_data['manifest_sha256'] == EXPECTED_SNAPSHOT and source_data['project_modules'] == 1210
        (D / 'source-audit.json').write_bytes(source_receipt.read_bytes())
    assert {name: sha(PROJECT / name) for name in FILES} == before
    assert sha(manifest) == EXPECTED_SNAPSHOT
    receipt = {'status': 'PASS_INDEPENDENT_DRIVER_CONTROLS', 'source_sha256': before,
               'snapshot_manifest_sha256': EXPECTED_SNAPSHOT,
               'toy_tests': {'exit': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr},
               'source_audit': {'exit': source.returncode, 'stdout': source.stdout,
                                'stderr': source.stderr, 'receipt_sha256': sha(D / 'source-audit.json')},
               'scope': 'Copied driver and control scripts; two-module test only. '
                        'The 1210-module snapshot is source-checked but not compiled here; '
                        'transitive package and dynamic provenance are not established.'}
    out = D / 'receipt.json'
    with out.open('x') as f:
        json.dump(receipt, f, indent=2, sort_keys=True); f.write('\n')
    print(receipt['status'], sha(out), flush=True)

if __name__ == '__main__':
    main()
