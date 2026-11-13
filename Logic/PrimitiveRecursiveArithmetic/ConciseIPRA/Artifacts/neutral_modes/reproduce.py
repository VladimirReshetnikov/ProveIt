"""Reproduce all code measurements and the 514-execution verification suite."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
for script, args in [
    ('tools/check_manifest.py', []),
    ('tools/measure.py', ['--check']),
    ('tools/check_duplicates.py', []),
    ('tools/verify_compact.py', []),
    ('tools/verify_strict.py', []),
]:
    subprocess.run([sys.executable, str(ROOT / script), *args], cwd=ROOT, check=True)
print('Reproduction completed: 180 compact and 334 strict executions; all expectations passed.')
