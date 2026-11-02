#!/usr/bin/env python3
"""Independent rerun of AQ26 toy controls for the related guard fix."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__: raise RuntimeError('audit requires assertions enabled')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
HIST=ROOT/'Computability/DiophantineConsistency/research/ipra-standard-aq26/historical'
commit='e4926948e0'
names=('test_history.py','test_prepare.py','test_freeze.py','test_real_extension.py','test_full_chain.py')
files=[HIST/n for n in (*names,'prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py','task-policy.json')]+[HIST.parent/'paired_plan.py']
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
before={str(p.relative_to(ROOT)):H(p) for p in files}
for p in files:
    raw=subprocess.check_output(['git','-C',str(ROOT),'show',commit+':'+str(p.relative_to(ROOT))])
    assert hashlib.sha256(raw).hexdigest()==H(p)
rows=[]
for name in names:
    for opt in (False,True):
        cmd=[sys.executable]+(['-O'] if opt else [])+[str(HIST/name)]
        p=subprocess.run(cmd,cwd=HIST,capture_output=True,text=True,timeout=240,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        if opt:assert p.returncode and 'controls require Python assertions enabled' in p.stderr
        else:assert p.returncode==0,(name,p.returncode,p.stdout,p.stderr)
        rows.append({'name':name,'optimized':opt,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    print('PASS: AQ26 toy control',name,flush=True)
assert {str(p.relative_to(ROOT)):H(p) for p in files}==before
out=HERE/'aq26-controls-receipt.json';assert not out.exists();out.write_text(json.dumps({'status':'PASS_AQ26_TOY_CONTROLS','workflow_commit':commit,'input_hashes':before,'subprocesses':rows,'scope':'Toy controls only; no real parent pair or AQ26 replay.'},indent=2,sort_keys=True)+'\n')
print('PASS_AQ26_TOY_CONTROLS',H(out),flush=True)
