#!/usr/bin/env python3
"""Check the integration payload and optional clean temporary patch application."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integration', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--apply-check', action='store_true', help='also use local Git in a temporary directory')
    parser.add_argument('--new-tests', action='store_true', help='execute the two new test modules (18 tests)')
    args = parser.parse_args()
    root = args.integration.resolve()
    proof = json.loads((root / 'PROVENANCE.json').read_text())
    for item in proof['files']:
        data = (root / item['path']).read_bytes()
        if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            raise SystemExit('payload hash mismatch: ' + item['path'])
    checked = dict(payload_hashes=len(proof['files']), pin=proof['pin'])
    if args.apply_check:
        with tempfile.TemporaryDirectory(prefix='proveit-patch-check-') as temporary:
            clean = Path(temporary)
            subprocess.run(['git', 'init', '--quiet'], cwd=clean, check=True)
            for item in proof['modified_or_added']:
                if item['status'] == 'modified':
                    if item['path'].split('/')[-1] != 'weighted_orbit_verify.py':
                        raise SystemExit('unknown pristine source dependency')
                    target = clean / item['path']
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes((root / proof['baseline_verifier']).read_bytes())
            patch = str(root / proof['patch'])
            subprocess.run(['git', 'apply', '--check', patch], cwd=clean, check=True)
            subprocess.run(['git', 'apply', patch], cwd=clean, check=True)
            for item in proof['modified_or_added']:
                if (clean / item['path']).read_bytes() != (root / 'overlay' / item['path']).read_bytes():
                    raise SystemExit('applied source differs: ' + item['path'])
            checked['clean_temporary_git_apply'] = True
            checked['applied_source_files'] = len(proof['modified_or_added'])
    snapshot = root / 'native_snapshot'
    smoke = r'''
import json, pathlib, sys, unittest
root = pathlib.Path(sys.argv[1]).resolve()
sys.path.insert(0, str(root))
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from fastunknot.normal_chamber_graph import normal_chamber_graph
from fastunknot.normal_chamber_graph_verify import verify_normal_chamber_graph
from tests.test_normal_chamber_graph import NormalChamberGraphTests
from normal_orbit_research.fixtures import layered_torus
count = unittest.TestLoader().loadTestsFromNames([
    'tests.test_weighted_run_rope', 'tests.test_normal_chamber_graph']).countTestCases()
if count != 18:
    raise AssertionError(count)
NormalChamberGraphTests.setUpClass()
raw, rows = layered_torus(1)
for name, module in list(sys.modules.items()):
    if name == 'fastunknot' or name.startswith('fastunknot.'):
        pathlib.Path(module.__file__).resolve().relative_to(root)
print(json.dumps({'new_tests_declared': count,
                  'corpus_cases_loaded': len(NormalChamberGraphTests.bank),
                  'fixture_tetrahedra': len(rows), 'tests_executed': 0}))
'''
    completed = subprocess.run([sys.executable, '-B', '-c', smoke, str(snapshot)],
                               cwd=snapshot, capture_output=True, text=True, check=True)
    checked['import_smoke'] = json.loads(completed.stdout)
    if args.new_tests:
        subprocess.run([sys.executable, '-B', '-m', 'unittest',
                        'tests.test_weighted_run_rope', 'tests.test_normal_chamber_graph', '-v'],
                       cwd=snapshot, check=True)
        checked['new_tests_executed'] = 18
    print(json.dumps(checked, indent=2))


if __name__ == '__main__':
    main()
