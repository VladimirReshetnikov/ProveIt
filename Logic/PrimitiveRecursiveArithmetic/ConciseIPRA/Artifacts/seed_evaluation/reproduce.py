"""Reproduce both SeedEval comparisons and the suspended-unit size experiment."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    subprocess.run([sys.executable, str(ROOT / 'code' / 'reproduce.py')], check=True)
    subprocess.run([sys.executable, str(ROOT / 'goal_code' / 'validate.py')], check=True)
    unit = ROOT / 'notes' / 'unit_experiment'
    subprocess.run([sys.executable, str(unit / 'measure_verify.py')], check=True)
    target = ROOT / 'evidence'
    target.mkdir(exist_ok=True)
    for name in ['verification', 'metrics', 'provenance']:
        shutil.copyfile(ROOT / 'code' / 'evidence' / (name + '.json'), target / (name + '.json'))
    shutil.copyfile(target / 'verification.json', target / 'validation.json')
    for name in ['verification', 'metrics']:
        shutil.copyfile(ROOT / 'goal_code' / 'evidence' / (name + '.json'),
                        target / ('latest_goal_' + name + '.json'))
    shutil.copyfile(unit / 'metrics_verification.json', target / 'unit_metrics_verification.json')
    print(json.dumps({'status': 'Both SeedEval comparisons and the unit experiment passed',
                      'evidence': str(target)}, indent=2))


if __name__ == '__main__':
    main()
