#!/usr/bin/env python3
"""Rebuild and independently check this package, from any working directory."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parent
before={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [R/'generated/signed10_b2.json',R/'generated/source_records.json']}
for script in ['build.py','independent_check.py']:
    subprocess.run([sys.executable,str(R/script)],cwd=R,check=True)
after={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [R/'generated/signed10_b2.json',R/'generated/source_records.json']}
if before!=after:raise RuntimeError('Delivered circuit or source records differ from rebuild')
receipt={'status':'PASS','byte_identical_rebuild':before,'independent_checker':'independent_check.py'}
(R/'generated/REPRODUCTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
