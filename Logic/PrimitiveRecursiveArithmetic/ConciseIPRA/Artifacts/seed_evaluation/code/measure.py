"""Measure all complete acceptance modules without running proof fixtures."""
import json
from pathlib import Path
import sys

from verify import measurements

ROOT = Path(__file__).resolve().parent
FILES = ['checker.py', 'control_step.py', 'seed_literal.py',
         'control_step_literal.py', 'control_computation_transport.py']


def main():
    report = {'python': sys.version,
              'programs': {name: measurements(ROOT / name) for name in FILES}}
    destination = ROOT / 'evidence'
    destination.mkdir(exist_ok=True)
    (destination / 'metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return report


if __name__ == '__main__':
    main()
