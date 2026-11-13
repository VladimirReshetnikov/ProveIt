"""Reproduce finite evidence. Build the standalone report with pdflatex separately."""
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
for name in ['build_transport_packet.py', 'verify.py', 'check_packet_traces.py',
             'check_normalization_boundary.py', 'measure_frontier.py']:
    subprocess.run([sys.executable, str(ROOT / 'code' / name)],
                   cwd=ROOT / 'code', check=True)
for name in ['verification.json', 'bounded_conversion_trace.json']:
    shutil.copy2(ROOT / 'code' / name, ROOT / 'evidence' / name)
print('All finite verification and measurement tasks completed.')
