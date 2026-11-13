#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-p-retry01';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'25162255201f1d14e6c2be0f1f140f0f9b3facab02f91633b9f2dd3f65f0b675','provider_survey.py':'2c3c9a64d8778dfbda7a55663e4ff73179e4d042e9caa0238b5bda3124fbf99d','source-manifest.json':'f7160b82b506b271f9911b87bdfc624eeadbba8aa14241d55ce54a4cbb3bd59b'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33ForwardNormP';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='fccbcedbe2384a7957070704048ccc9f19dff2a414ac42a9c5329956e2a78166' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33ConstructorEllRetry']
old=(d/'research/nine-sharing-sign33-forward-norm-p-check/src/DiophantineConsistency/Sign33ForwardNormP.lean').read_text();assert old.replace('Sign33ForwardNormPEll','Sign33ConstructorEllRetry')==s
for x in ['ι tau = d.tau','d.P = 1','ι (v 27)*ι (v 27)-ι (v 21)*(ι (v 21)+((ι (v 11)+1)+(ι (v 12)+1))) = 1','Sign33ConstructorEllRetry.ell_of_core','d.tau ^ 2 - d.ell*(d.ell+d.k) = 1 at hp']:assert x in s
survey=(p/'provider_survey.py').read_text();assert 'ac57f166f4da6cb14f928abd3914ed06a0178859c177836e107efd7e431fece8' in survey and 'Sign33ConstructorEllRetry' in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional P and tau representative to constructor cut; no Lean replay'},indent=2,sort_keys=True))
