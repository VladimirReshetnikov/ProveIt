#!/usr/bin/env python3
"""Rerun the actual bounded-shear wrapper on an isolated exact-byte tree."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('review requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/frontier13-low-degree-shear-obstruction';PORT=BASE/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';meta=json.loads(PORT.read_text())['coefficient_binding']['ports']['beta']
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();files=[Path(__file__),TASK/'run.py',TASK/'check.py',TASK/'receipt.json',BASE/'research/adaptive-square-sums/candidate.json',PORT,PORT.parent/'coefficients'/meta['file'],BASE/'reviews/frontier13-pdf-historical-lean-binding-independent-audit/receipt.json'];before={str(p.resolve()):H(p) for p in files}
with tempfile.TemporaryDirectory(prefix='independent-shear-wrapper-') as tmp:
 dest=Path(tmp)/'Computability/DiophantineConsistency'
 for src in files[1:]:
  if src==TASK/'receipt.json':continue
  q=dest/src.relative_to(BASE);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,q)
 t=dest/'research/frontier13-low-degree-shear-obstruction'
 p=subprocess.run([sys.executable,str(t/'run.py')],capture_output=True,text=True,timeout=120)
 assert p.returncode==0 and p.stdout.startswith('PASS_BOUNDED_SHEAR_OBSTRUCTION '),(p.returncode,p.stdout,p.stderr)
 assert json.loads((t/'receipt.json').read_text())==json.loads((TASK/'receipt.json').read_text()) and p.stdout.strip().endswith(H(t/'receipt.json'))
 again=subprocess.run([sys.executable,str(t/'run.py')],capture_output=True,text=True,timeout=30)
 assert again.returncode!=0 and 'refusing to overwrite receipt' in again.stderr
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_SHEAR_WRAPPER','inputs_sha256':before,'fresh_wrapper_exit':p.returncode,'fresh_wrapper_stdout':p.stdout,'second_wrapper_exit':again.returncode,'second_wrapper_stderr':again.stderr,'scope':'Process-wrapper reproduction and no-overwrite control only.'};path=HERE/'wrapper-receipt.json'
if path.exists():raise ValueError('refusing to overwrite receipt')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
