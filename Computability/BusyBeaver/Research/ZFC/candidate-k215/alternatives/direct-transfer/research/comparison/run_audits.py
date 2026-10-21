#!/usr/bin/env python3
"""Run both independent finite audits using only files in this directory."""
from pathlib import Path
import argparse, subprocess, sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Do not use Python -O.')
p=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=p/'replayed-evidence');a=ap.parse_args()
out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
common=['--table',str(p/'candidate.native.tm'),'--source',str(p/'source.sites.json'),'--out',str(out)]
subprocess.run([sys.executable,'-B',str(p/'audit_short215.py'),*common,
 '--reference-source',str(p/'reference-source.sites.json'),
 '--comparison-inputs',str(p/'comparison-inputs')],check=True)
subprocess.run([sys.executable,'-B',str(p/'audit_runtime_metadata.py'),*common,
 '--runtime',str(p/'runtime'),'--mapping',str(p/'native-to-legacy.json')],check=True)
print('Both finite independent audits passed. See the scope statements in the reports.')
