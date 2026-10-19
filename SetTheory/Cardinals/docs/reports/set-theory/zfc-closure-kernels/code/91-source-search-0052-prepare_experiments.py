#!/usr/bin/env python3
"""Restore the historical directory layout for optional discovery reruns."""
from pathlib import Path
import gzip
import shutil
import subprocess
import sys

HERE=Path(__file__).resolve().parent
assert __debug__, 'Use ordinary Python with assertions enabled.'
subprocess.run([sys.executable,str(HERE/'verify.py'),'--prepare-only'],check=True)
base=HERE/'build/reference/zfc245-proof-20261018'
shutil.copytree(base,HERE/'work/machine_reduction/base/zfc245-proof-20261018',dirs_exist_ok=True)
shutil.copytree(HERE/'build/runtime',HERE/'work/fine_grammar/runtime',dirs_exist_ok=True)
fixture=base/'inputs/state_reduction/candidate245-literal-cases.txt.gz'
with gzip.open(fixture,'rb') as f:
    (HERE/'work/machine_reduction/candidate245-literal-cases.txt').write_bytes(f.read())
print('Prepared historical runtime locations and decompressed the exact fixture. No search was started.')
