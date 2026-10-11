#!/usr/bin/env python3
"""Run the five independent checks on temporary copies, retaining fresh JSONs."""
from pathlib import Path
import argparse
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
CHECKS = (
    ('check_beta.py', 'beta_checks.json'),
    ('centered_checks.py', 'centered_checks.json'),
    ('check_quartic.py', 'quartic_checks.json'),
    ('verify_collision.py', 'collision_verification.json'),
    ('verify_derivative_pair.py', 'derivative_pair_verification.json'),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'verification/reproduced')
    args = parser.parse_args()
    destination = args.output_dir.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='proveit-reflection-checks-') as temp:
        workspace = Path(temp)
        for script, report in CHECKS:
            shutil.copyfile(ROOT / 'verification' / script, workspace / script)
            print('\nRunning ' + script, flush=True)
            subprocess.run([sys.executable, str(workspace / script)], cwd=workspace, check=True)
            shutil.copyfile(workspace / report, destination / report)
    print('\nAll five scripts completed. Fresh records:', destination, flush=True)


if __name__ == '__main__':
    main()
