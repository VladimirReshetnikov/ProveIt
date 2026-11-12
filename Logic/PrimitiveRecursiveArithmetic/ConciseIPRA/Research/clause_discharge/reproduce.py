"""Run the meaningful implementation checks and recompute complete source sizes."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    commands = [
        ['validation/verify_translation.py'],
        ['validation/run_independent_audit.py', 'code/checker_deterministic.py',
         'validation/examples', '--output', 'validation/independent_results.json'],
        ['validation/verify_fuel.py'],
        ['measure.py'],
    ]
    for command in commands:
        subprocess.run([sys.executable, *command], cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
