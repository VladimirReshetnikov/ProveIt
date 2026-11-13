#!/usr/bin/env python3
"""Retain external display-check output without changing the displayed files."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
parser = argparse.ArgumentParser()
parser.add_argument('--variant', choices=('94', '95'), default='95')
args = parser.parse_args()
OUT = HERE/'observations'/f'display-check-{args.variant}-attempt01'
OUT.mkdir(parents=True,exist_ok=False)
run = subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'check_display.py'), '--variant', args.variant],
                     cwd=ROOT,capture_output=True,text=True,timeout=180)
(OUT/'stdout').write_text(run.stdout); (OUT/'stderr').write_text(run.stderr)
receipt={'variant':args.variant, 'exit_code':run.returncode,
         'checker_sha256':sha256((HERE/'check_display.py').read_bytes()).hexdigest(),
         'capture_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
         'stdout_sha256':sha256((OUT/'stdout').read_bytes()).hexdigest(),
         'stderr_sha256':sha256((OUT/'stderr').read_bytes()).hexdigest()}
(OUT/'terminal.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
if run.returncode or run.stderr or json.loads(run.stdout)['status'] != 'EXTERNAL_TEX_PDF_DISPLAY_CHECK_PASS':
    raise RuntimeError('display check failed; observation retained')
print('CAPTURED_EXTERNAL_DISPLAY_CHECK')
