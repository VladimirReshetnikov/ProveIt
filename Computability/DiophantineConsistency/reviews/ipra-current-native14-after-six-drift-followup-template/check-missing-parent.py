#!/usr/bin/env python3
"""Fail-closed missing-parent probe; no positive preparation or replay."""
import hashlib,json,subprocess,sys,tempfile
from pathlib import Path
D=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();names=('prepare.py','replay.py');before={n:H(D/n) for n in names};checker=H(__file__)
for n in names:compile((D/n).read_text(),str(D/n),'exec')
with tempfile.TemporaryDirectory(prefix='ipra14-after107-missing-parent-') as root:
 p=Path(root);out=p/'output';args=[str(out),str(p/'missing-a'),str(p/'missing-b'),str(p/'missing-author'),str(p/'missing-peer'),str(p/'missing-wrapper-a'),str(p/'missing-wrapper-b')]
 proc=subprocess.run([sys.executable,str(D/'prepare.py'),*args],capture_output=True,text=True)
 assert proc.returncode!=0 and not out.exists() and str(p/'missing-a'/'receipt.json') in proc.stderr
 row={'exit_code':proc.returncode,'stdout':proc.stdout,'stderr':proc.stderr,'output_created':out.exists()}
assert {n:H(D/n) for n in names}==before and H(__file__)==checker
receipt={'status':'PASS_MISSING_PARENT_REJECTED','checker_sha256':checker,'files_sha256':before,'row':row,'scope':'Both draft scripts compile; the preparer rejects a missing comparator receipt before creating output. No parent-dependent preparation or Lean replay was performed.'}
path=D/'missing-parent-receipt.json'
with path.open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
print('PASS_MISSING_PARENT_REJECTED',H(path))
