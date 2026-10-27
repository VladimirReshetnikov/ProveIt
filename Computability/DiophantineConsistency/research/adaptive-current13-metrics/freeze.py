"""Authenticate and freeze the completed finite-only author packet."""
from pathlib import Path
import hashlib
import json
import shutil

H=Path(__file__).resolve().parent
D=H.parents[1]


def require(b,m):
    if not b: raise RuntimeError(m)


def pin(p):
    raw=p.read_bytes()
    return {'path':str(p.relative_to(D)),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


require(not (H/'FILES.json').exists() and not (H/'REPLAY.json').exists(),'Freeze once')
observations=[]
for name in ('INPUTS.json','SUPPLEMENT.json'):
    for r in json.loads((H/name).read_text())['files']:
        actual=pin(D/r['path']); require(actual==r,'Current input '+r['path']); observations.append(actual)
records=[]
for i in range(1,5):
    out=H/'attempts'/str(i); state=json.loads((out/'state.json').read_text())
    require(state['status']=='PASS' and state['exit_code']==0 and state['sources_unchanged'],'Attempt result')
    for r in state['sources']:
        p=out/Path(r['path']).name
        require(hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'],'Exact attempted source snapshot')
    for key,name in (('stdout','stdout.log'),('timing','timing.log'),('certificate','CERTIFICATE.json')):
        require(pin(out/name)['sha256']==state[key]['sha256'],'Attempt artifact '+key)
    records.append({'attempt':i,'state':pin(out/'state.json'),'mode':state['mode'],
                    'exit_code':state['exit_code'],'seconds':state['seconds'],
                    'stdout':pin(out/'stdout.log'),'timing':pin(out/'timing.log'),
                    'certificate':pin(out/'CERTIFICATE.json')})
require(len({(H/'attempts'/str(i)/'stdout.log').read_bytes() for i in (2,3,4)})==1,'Final complete stdout identity')
require(len({(H/'attempts'/str(i)/'CERTIFICATE.json').read_bytes() for i in (2,3,4)})==1,'Final complete certificate identity')
cert=json.loads((H/'CERTIFICATE.json').read_text())
for key in ('auditor','graph_pin','metric_proof','input_manifest','definition_supplement'):
    r=cert[key]; require(pin(D/r['path'])==r,'Final source pin '+key)
require((H/'CERTIFICATE.json').read_bytes()==(H/'attempts/4/CERTIFICATE.json').read_bytes(),'Final certificate')
require(shutil.disk_usage(H).free>=512*1024**2,'Final reserve')
replay={'status':'AUTHOR_PASS','scope':'Finite-only author audit, no Lean builds; independent review remains separate',
        'artifacts':{n:pin(H/n) for n in ('polynomial.json','CERTIFICATE.json','PROOF.md','README.md')},
        'source_files':{n:pin(H/n) for n in ('audit.py','prepare.py','run.py','freeze.py')},
        'input_observations':observations,'runs':records,'failed_attempts':0,
        'normal_optimized_full_certificate_and_stdout_identical':True,
        'new_lean_builds':0,'free_bytes':shutil.disk_usage(H).free}
(H/'REPLAY.json').write_text(json.dumps(replay,sort_keys=True,indent=2)+'\n')
files=[pin(p) for p in sorted(H.rglob('*')) if p.is_file()]
(H/'FILES.json').write_text(json.dumps(files,sort_keys=True,indent=2)+'\n')
print(json.dumps({'replay':pin(H/'REPLAY.json'),'files':len(files),'manifest':pin(H/'FILES.json')},indent=2))
