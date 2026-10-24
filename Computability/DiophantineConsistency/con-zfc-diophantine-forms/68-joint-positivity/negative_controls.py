"""A byte-tamper control, distinct from mathematical mutation checks."""
from pathlib import Path
import tempfile,shutil,subprocess,sys
R=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix='conzfc-tamper-') as t:
 d=Path(t)/'release';shutil.copytree(R,d)
 p=d/'integer_system/octic28.json';p.write_bytes(p.read_bytes()+b' ')
 r=subprocess.run([sys.executable,str(d/'verify.py')],capture_output=True,text=True)
 if r.returncode==0 or 'manifest integer_system/octic28.json' not in r.stderr:raise ValueError('tamper not rejected for expected reason')
print('PASS: changed-byte manifest control rejected before executing a checker')
print('Mathematical mutation controls are separately implemented in packing/audit.py and direct_audit/check.py.')
