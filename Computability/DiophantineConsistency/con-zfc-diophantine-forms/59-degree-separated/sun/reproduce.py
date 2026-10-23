#!/usr/bin/env python3
"""Rebuild byte-identical artifacts and run the independent audits twice."""
from pathlib import Path
import hashlib, subprocess, sys
R=Path(__file__).resolve().parent
files=[R/'generated'/n for n in ('sun10.json','source_records.json','METRICS.json')]
before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
subprocess.run([sys.executable,str(R/'build.py')],check=True)
for p,h in before.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('Rebuild differs: '+p.name)
for flags in ([],['-O']):subprocess.run([sys.executable,*flags,str(R/'independent_check.py')],check=True)
print('PASS: byte-identical rebuild and both independent audit modes')
