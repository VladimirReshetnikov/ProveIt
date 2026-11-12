"""Replay the delivered certificates and reproduce checker measurements."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    for script in ['verify_manifest.py', 'verify.py', 'verify_fuel.py', 'measure.py']:
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    print('All verification and measurement steps completed')


if __name__ == '__main__':
    main()
