"""Reproduce incumbent evidence and optionally rebuild the research PDF."""
import argparse
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--pdf', action='store_true')
args = parser.parse_args()
for script in ('reproduce_frontier.py', 'reproduce_whole_json.py'):
    subprocess.run([sys.executable, str(root / 'audit' / script)],
                   cwd=root, check=True)
if args.pdf:
    subprocess.run([sys.executable, str(root / 'build_pdf.py')],
                   cwd=root, check=True)
print('Reproduction completed; no new below-frontier claim is implied.')
