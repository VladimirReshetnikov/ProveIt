#!/usr/bin/env python3
"""Fail-closed probes only; no positive comparison is claimed."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
D=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=('prepare.py','replay.py','compare.py','run.py');before={n:H(D/n) for n in files};self_hash=H(__file__)
for n in files:compile((D/n).read_text(),str(D/n),'exec')
rows=[]
with tempfile.TemporaryDirectory(prefix='ipra-six-drift-negative-') as tmp:
 root=Path(tmp);x,y,z=(root/n for n in ('x','y','z'))
 for p in (x,y,z):p.mkdir()
 (x/'state.json').write_text('{}');(y/'state.json').write_text('{}');os.link(x/'state.json',z/'state.json')
 for script in ('compare.py','run.py'):
  for case,a,b in (('missing_plan',x,y),('same_directory',x,x),('same_state_inode',x,z)):
   w=root/(script.removesuffix('.py')+'-'+case);w.mkdir()
   for n in ('compare.py','run.py'):shutil.copyfile(D/n,w/n);assert H(w/n)==before[n]
   plan=root/'missing-plan';p=subprocess.run([sys.executable,str(w/script),str(plan),str(a),str(b)],capture_output=True,text=True)
   assert p.returncode!=0 and not (w/'receipt.json').exists() and not (w/'terminal.json').exists()
   if case=='missing_plan':assert 'FileNotFoundError:' in p.stderr.splitlines()[-1] and str(plan/'manifest.json') in p.stderr.splitlines()[-1]
   else:assert 'author and peer must be independent runs' in p.stderr
   rows.append({'script':script,'case':case,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
assert {n:H(D/n) for n in files}==before and H(__file__)==self_hash
out={'status':'PASS_FAIL_CLOSED_NEGATIVE_CHECKS','files_sha256':before,'checker_sha256':self_hash,'rows':rows,
     'scope':'Both scripts present in each isolated probe; syntax and missing-plan / identical-directory / shared-state-inode rejection only. No successful comparison or replay is claimed.'}
path=D/'comparator-negative-checks.json'
with path.open('x') as f:json.dump(out,f,indent=2,sort_keys=True);f.write('\n')
print('PASS_FAIL_CLOSED_NEGATIVE_CHECKS',len(rows),H(path))
