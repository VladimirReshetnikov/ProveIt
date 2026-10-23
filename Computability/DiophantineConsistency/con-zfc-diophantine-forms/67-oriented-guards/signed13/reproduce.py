#!/usr/bin/env python3
from pathlib import Path
import hashlib, subprocess,sys
R=Path(__file__).resolve().parent
files=[p for p in (R/'generated').glob('*.json') if p.name!='CHECKS.json'];before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
subprocess.run([sys.executable,str(R/'build_jones.py')],check=True)
for p,h in before.items():
 if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('non-identical rebuild: '+p.name)
for flags in ([],['-O']):subprocess.run([sys.executable,*flags,str(R/'verify.py')],check=True)
print('PASS: byte-identical rebuild and normal/optimized verification')
