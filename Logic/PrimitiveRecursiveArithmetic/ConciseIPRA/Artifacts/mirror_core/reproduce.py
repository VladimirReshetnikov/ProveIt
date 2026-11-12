"""Replay the packaged checker evidence using only the Python standard library."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def main():
    for script in ['verify_mirror.py', 'verify_transformations.py', 'measure.py']:
        subprocess.run([sys.executable, str(ROOT / 'tests' / script)], cwd=ROOT, check=True)

if __name__ == '__main__':
    main()
