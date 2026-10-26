#!/usr/bin/env python3
"""Replay only the four standalone files in an existing pinned ProveIt checkout."""
import argparse
import json
import pathlib
import subprocess
import sys

EXPECTED_LEAN = 'leanprover/lean4:v4.32.0'
EXPECTED_MATHLIB = '81a5d257c8e410db227a6665ed08f64fea08e997'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('checkout', type=pathlib.Path)
a = p.parse_args()
checkout = a.checkout.resolve()
package = pathlib.Path(__file__).resolve().parents[1]
if (checkout / 'lean-toolchain').read_text().strip() != EXPECTED_LEAN:
    sys.exit('The checkout is not pinned to the expected Lean 4.32.0 toolchain.')
manifest = json.loads((checkout / 'lake-manifest.json').read_text())
mathlib = next(x for x in manifest['packages'] if x['name'] == 'mathlib')
if mathlib['rev'] != EXPECTED_MATHLIB:
    sys.exit('The checkout does not record the expected mathlib revision.')
for name in ['ControllerFixedPower', 'DegreeEnumeration', 'DegreeEnumerationDirect', 'AffineReflection']:
    source = package / 'lean' / (name + '.lean')
    result = subprocess.run(['lake', 'env', 'lean', str(source)], cwd=checkout,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print('\n###', name, 'exit', result.returncode, flush=True)
    print(result.stdout, end='', flush=True)
    if result.returncode or 'sorryAx' in result.stdout:
        sys.exit(result.returncode or 1)
print('\nAll standalone cores passed. No repository patches were applied or compiled.')
