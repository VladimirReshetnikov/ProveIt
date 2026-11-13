"""Run the distributed evidence checks without network access."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
for script in ["tests/verify.py", "tests/strict_audit.py", "tests/review_strict.py", "measure.py",
               "experiments/counter_vectors/verify_counter_vectors.py"]:
    subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
