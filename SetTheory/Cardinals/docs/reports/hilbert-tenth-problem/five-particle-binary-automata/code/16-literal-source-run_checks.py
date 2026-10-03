#!/usr/bin/env python3
"""Run all replay stages; a failed subprocess prevents a passing receipt."""
import subprocess,sys,json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parent
scripts=['check_primary_table.py','verify_virtual3.py','validate_source.py','verify_affine.py','independent_audit.py','class_expansion_ledger.py','test_loader.py','test_concrete.py']
results=[]
for s in scripts:
    r=subprocess.run([sys.executable,str(R/s)],cwd=R,text=True,capture_output=True)
    (R/(s+'.log')).write_text(r.stdout+r.stderr)
    if r.returncode:print(r.stdout+r.stderr);raise SystemExit(r.returncode)
    results.append(dict(script=s,status='passed'))
    print(s,'passed',flush=True)
optimized=[]
for script in scripts:
    r=subprocess.run([sys.executable,'-O',str(R/script)],cwd=R,text=True,capture_output=True)
    (R/(script+'.optimized.log')).write_text(r.stdout+r.stderr)
    if r.returncode:print(r.stdout+r.stderr);raise SystemExit(r.returncode)
    optimized.append(script)
out=dict(status='passed',stages=results,optimized_stages=optimized,source_sha256=hashlib.sha256((R/'source.json').read_bytes()).hexdigest())
(R/'all-checks-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
