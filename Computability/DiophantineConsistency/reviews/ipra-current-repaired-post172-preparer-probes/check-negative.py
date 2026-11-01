#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
D=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
names=('prepare.py','replay.py');before={n:H(D/n) for n in names};checker=H(__file__)
for n in names:compile((D/n).read_text(),str(D/n),'exec')
rows=[]
with tempfile.TemporaryDirectory(prefix='ipra-post172-negative-') as td:
 root=Path(td);exists=root/'existing';exists.mkdir();marker=exists/'marker';marker.write_text('preserve')
 cases=[('existing_output',[sys.executable,str(D/'prepare.py'),str(root/'missing-survey'),str(exists)],'refusing to overwrite'),('missing_survey',[sys.executable,str(D/'prepare.py'),str(root/'missing-survey'),str(root/'new')],'manifest.json'),('missing_manifest',[sys.executable,str(D/'replay.py'),'0'*64],'manifest.json')]
 for name,cmd,needle in cases:
  p=subprocess.run(cmd,capture_output=True,text=True);assert p.returncode!=0 and needle in p.stderr and marker.read_text()=='preserve' and not (root/'new').exists();rows.append({'case':name,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
assert {n:H(D/n) for n in names}==before and H(__file__)==checker
out={'status':'PASS_FAIL_CLOSED_NEGATIVE_CHECKS','files_sha256':before,'checker_sha256':checker,'rows':rows,'scope':'Existing output, missing survey and missing replay manifest are rejected; no positive replay.'}
p=D/'negative-checks.json'
with p.open('x') as f:json.dump(out,f,indent=2,sort_keys=True);f.write('\n')
print(out['status'],len(rows),H(p))
