"""Reproduce the finite evidence and measured source sizes."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
for relative, directory in [
    ("code/native/verify.py", root / "code/native"),
    ("code/check_observations.py", root),
    ("code/measure_sources.py", root),
]:
    subprocess.run([sys.executable, str(root / relative)], cwd=directory, check=True)
print("All finite checks and source measurements completed.")
