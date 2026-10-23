#!/usr/bin/env python3
"""Reproduce all coefficient payloads and 20 circuits, then verify them.

Usage: python3 reproduce.py
Requires Python 3.10 or later and its standard library only. No network,
external checkout, computer algebra package or TeX installation is needed.
The four materialized numerals, derived circuit packets and audit receipts
are deterministically rebuilt in place. Preserved upstream sources are
never modified. To check the supplied artifacts without rebuilding them,
run python3 verify.py instead.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def run(script, receipt=None):
    result = subprocess.run([sys.executable, '-B', str(ROOT/script)],
                            cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(script+' failed:\n'+result.stdout+result.stderr)
    data = json.loads(result.stdout)
    if receipt:
        (ROOT/receipt).write_text(json.dumps(data, indent=2)+'\n')
    print('PASS '+script, flush=True)
    return dict(script=script, status='PASS')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.parse_args()
    steps = [run('code/build_coefficients.py', 'evidence/coefficients_build.json'),
             run('code/audit_materialized_coefficients.py')]
    for name in ['build_optimized_1069.py', 'build_optimized_1073.py',
                 'build_optimized_1081.py', 'build_signed24.py',
                 'refactor_comparison_circuits.py', 'bind_coefficients.py']:
        steps.append(run('code/'+name))
    steps.append(run('verify.py'))
    result = dict(status='PASS', steps=steps, coefficient_payloads=4, circuits=20,
                  final_verification='evidence/FINAL_VERIFICATION.json',
                  scope='Complete offline reproduction of arithmetic artifacts; mathematical proofs remain separate.')
    (ROOT/'evidence/REPRODUCTION.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
