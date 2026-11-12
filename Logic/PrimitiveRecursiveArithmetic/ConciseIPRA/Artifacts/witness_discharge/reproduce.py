"""Reproduce the measurements and all delivered finite verification evidence."""
from pathlib import Path
import json
import platform
import shutil
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parent
    commands = [
        ['measure.py'],
        ['validation/verify.py'],
        ['validation/audit_normalization.py', 'code/checker.py',
         '--output', 'evidence/normalization_verification.json'],
        ['validation/verify_fuel.py'],
    ]
    for arguments in commands:
        subprocess.run([sys.executable] + arguments, cwd=root, check=True)
    shutil.copyfile(root / 'validation/verification.json',
                    root / 'evidence/proof_verification.json')
    receipt = dict(status='PASS', python=platform.python_version(),
                   commands=[[sys.executable] + c for c in commands],
                   note='Finite executable evidence; universal theorems are written proofs.')
    (root / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('All measurements and verification suites passed.')


if __name__ == '__main__':
    main()
