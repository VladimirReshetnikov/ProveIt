#!/usr/bin/env python3
"""Rebuild the direct Cantor dependency without changing the score overlay."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

D=Path(__file__).resolve().parent
M=D/'manifest.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=M.read_bytes();m=json.loads(raw);mh=hashlib.sha256(raw).hexdigest()
assert len(sys.argv)==2 and sys.argv[1]==mh and H(D/'replay.py')==m['guard'][str(D/'replay.py')]
roots=m['roots'];env=dict(os.environ,LEAN_PATH=':'.join(roots),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
def audit():
    assert H(M)==mh
    for path,digest in m['guard'].items():assert Path(path).is_file() and H(path)==digest,path
    for records in m['candidates'].values():
        for path,info in records.items():
            p=Path(path)
            if info is None:assert not os.path.lexists(p),path
            else:assert p.is_file() and str(p.resolve())==info['resolved'] and H(p)==info['sha256'],path
    dep=subprocess.run([m['lean'],'--deps',m['source']],env=env,cwd=m['root'],capture_output=True,text=True,check=True)
    assert dep.stdout==m['deps_stdout'] and not dep.stderr
audit()
w=Path(tempfile.mkdtemp(prefix='gap85-score-cantor-repair-'))
obj=w/'BusyBeaver/ZFC/ArithmeticCantor.olean';obj.parent.mkdir(parents=True)
shutil.copyfile(m['source'],w/'ArithmeticCantor.lean');shutil.copyfile(M,w/'manifest.json');shutil.copyfile(D/'replay.py',w/'replay.py')
state={'status':'RUNNING','root':str(w),'manifest_sha256':mh,'source_sha256':m['source_sha256'],
       'direct_imports':m['selected'],'original_provider_status':m['original_provider_status'],
       'original_failure':m['original_failure'],'scope':m['scope']}
def save(): (w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
save();print('ROOT',w,flush=True)
try:
    assert H(w/'ArithmeticCantor.lean')==m['source_sha256']
    # Deliberately preserve the historical no---root invocation and source path.
    cmd=[m['lean'],'-M6000','-j1','-DElab.async=false','-o',str(obj),m['source']]
    with (w/'lean.log').open('w') as log:
        result=subprocess.run(cmd,env=env,cwd=m['root'],stdout=log,stderr=subprocess.STDOUT)
    text=(w/'lean.log').read_text()
    state.update(command=cmd,exit_code=result.returncode,log_sha256=H(w/'lean.log'),
                 object_sha256=H(obj) if obj.is_file() else None,
                 warnings=[line for line in text.splitlines() if 'warning:' in line])
    save()
    assert result.returncode==0 and 'error:' not in text and 'sorryAx' not in text
    assert state['object_sha256']==m['expected_olean_sha256'],state['object_sha256']
    assert state['log_sha256']==m['old_cantor_log_sha256'],state['log_sha256']
    assert len(state['warnings'])==5,state['warnings']
    audit();assert H(w/'ArithmeticCantor.lean')==m['source_sha256'] and H(obj)==m['expected_olean_sha256']
    state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as exc:
    state.update(status='FAILED',failure=repr(exc));save();print('FAILED',repr(exc),flush=True);raise
