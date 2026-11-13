#!/usr/bin/env python3
"""Rerun the actual process wrapper in an isolated exact-byte copy."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('review requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];RESEARCH=ROOT/'Computability/DiophantineConsistency/research';TASK=RESEARCH/'frontier13-local-rewrite-screen'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=[Path(__file__),TASK/'run.py',TASK/'screen.py',TASK/'receipt.json',RESEARCH/'adaptive-square-sums/candidate.json',RESEARCH/'adaptive-direct-ordinate86/candidate.json'];before={str(p.resolve()):H(p) for p in files}
with tempfile.TemporaryDirectory(prefix='independent-rewrite-wrapper-') as tmp:
 r=Path(tmp);t=r/'frontier13-local-rewrite-screen';t.mkdir()
 for n in ('run.py','screen.py'):shutil.copy2(TASK/n,t/n)
 for folder in ('adaptive-square-sums','adaptive-direct-ordinate86'):
  (r/folder).mkdir();shutil.copy2(RESEARCH/folder/'candidate.json',r/folder/'candidate.json')
 p=subprocess.run([sys.executable,str(t/'run.py')],capture_output=True,text=True,timeout=120)
 assert p.returncode==0 and p.stdout.startswith('PASS_BOUNDED_SCREEN '),(p.returncode,p.stdout,p.stderr)
 result=json.loads((t/'receipt.json').read_text());original=json.loads((TASK/'receipt.json').read_text())
 assert result==original and p.stdout.strip().endswith(H(t/'receipt.json'))
 again=subprocess.run([sys.executable,str(t/'run.py')],capture_output=True,text=True,timeout=30)
 assert again.returncode!=0 and 'refusing to overwrite receipt' in again.stderr
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_BOUNDED_SCREEN_WRAPPER','inputs_sha256':before,'fresh_wrapper_exit':p.returncode,'fresh_wrapper_stdout':p.stdout,'second_wrapper_exit':again.returncode,'second_wrapper_stderr':again.stderr,'scope':'Process-wrapper reproduction and no-overwrite check only.'};path=HERE/'wrapper-receipt.json'
if path.exists():raise ValueError('refusing to overwrite receipt')
path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(path))
