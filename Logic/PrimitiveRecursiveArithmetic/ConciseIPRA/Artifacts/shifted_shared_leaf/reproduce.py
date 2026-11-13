"""Recompute measurements and execute the supplied proof-certificate checks."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
(ROOT / 'evidence').mkdir(exist_ok=True)
metrics = subprocess.run([sys.executable, str(ROOT / 'measure.py')],
                         check=True, capture_output=True)
(ROOT / 'evidence/metrics.json').write_bytes(metrics.stdout)
subprocess.run([sys.executable, str(ROOT / 'verify.py')], check=True)
subprocess.run([sys.executable, str(ROOT / 'verify_negative.py')], check=True)
print('Measurements and certificate checks completed.')
