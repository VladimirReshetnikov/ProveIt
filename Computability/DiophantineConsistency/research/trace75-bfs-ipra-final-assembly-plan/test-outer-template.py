#!/usr/bin/env python3
"""Exercise an isolated outer-wrapper copy with stub children; never invokes Lean."""
from hashlib import sha256
from pathlib import Path
import json,subprocess,sys,tempfile

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent
template=(h/'run-outer-template.py').read_text()
def digest(p): return sha256(p.read_bytes()).hexdigest()
def trial(mode):
    with tempfile.TemporaryDirectory(prefix='trace75-assembly-wrapper-policy-') as td:
        d=Path(td); obs=d/'observations'; (obs/'preflight-attempt01').mkdir(parents=True)
        (obs/'policy-attempt01').mkdir();pre=obs/'preflight-attempt01/terminal.json';policy=obs/'policy-attempt01/result.json'
        pre.write_text('{}\n');policy.write_text('{}\n')
        body='''from pathlib import Path\nimport json,sys\nh=Path(__file__).resolve().parent\no=h/'observations'/'attempt01'\no.mkdir(parents=True)\n'''
        if mode=='pass':body+="(o/'result.json').write_text(json.dumps({'status':'PASS'}))\n"
        elif mode=='failed':body+="(o/'result.json').write_text(json.dumps({'status':'FAILED'}))\n"
        elif mode=='malformed':body+="(o/'result.json').write_text('{broken')\n"
        elif mode=='exit':body+="(o/'result.json').write_text(json.dumps({'status':'PASS'}))\nsys.exit(7)\n"
        elif mode not in {'missing','drift'}:raise RuntimeError('bad test mode')
        if mode=='drift':body+="(o/'result.json').write_text(json.dumps({'status':'PASS'}))\n"
        child=d/'run.py';child.write_text(body)
        text=template.replace('TO_BE_PINNED_AFTER_PARENT_TERMINAL',digest(child)).replace('TO_BE_PINNED_AFTER_PREFLIGHT',digest(pre)).replace('TO_BE_PINNED_AFTER_POLICY',digest(policy))
        wrapper=d/'wrapper.py';wrapper.write_text(text)
        if mode=='drift':child.write_text(body+'\n# changed after pin\n')
        proc=subprocess.run([sys.executable,'-I','-S','-B',str(wrapper),'--attempt','attempt01'],capture_output=True,text=True)
        terminal=obs/'outer-attempt01/terminal.json'
        return proc.returncode, json.loads(terminal.read_text()) if terminal.is_file() else None
tests={}
for mode in ['pass','failed','malformed','missing','exit','drift']:
    code,terminal=trial(mode)
    if mode=='pass':tests['accept_pass']=code==0 and terminal is not None and terminal['child_status']=='PASS' and terminal['exit']==0
    elif mode=='drift':tests['reject_input_drift']=code!=0 and terminal is None
    else:tests['reject_'+mode]=code!=0 and terminal is not None
print(json.dumps({'status':'PASS' if all(tests.values()) else 'FAIL','tests':tests,
                  'scope':'isolated stub wrapper controls only; no parent read and no Lean'},sort_keys=True))
raise SystemExit(0 if all(tests.values()) else 1)
