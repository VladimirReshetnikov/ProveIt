from pathlib import Path
import hashlib,json,re,shutil
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
P=Path('/tmp/arithmetic-dag-loops-peer-v9mmg0s_')
def require(b,m):
    if not b: raise RuntimeError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p);return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def save(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
observations=[]
def check(r):
    require(sha(r['path'])==r['sha256'],'hash '+r['path'])
    observations.append(dict(path=r['path'],sha256=r['sha256']))
state=json.loads((P/'PEER.json').read_text())
require(state['status']=='FAILED' and state['failure']=='report mismatch BusyBeaver.ZFC.ArithmeticDagLoopsChecks','exact harness-only failure')
check(state['inputs']);check(state['driver'])
inputs=json.loads(Path(state['inputs']['path']).read_text())
for r in inputs['initial_observations']:check(r)
expected={r['module']:r for r in inputs['expected']}
require(len(state['records'])==8 and len(expected)==8,'eight commands')
records=[]
for r in state['records']:
    for k in ['source','snapshot','log','timing','object']:check(r[k])
    e=expected[r['module']]
    require(r['exit_code']==0,'Lean exit')
    require(all(r['source'][k]==e['source'][k] for k in ['path','sha256']),'source record')
    require(r['source']['sha256']==r['snapshot']['sha256'],'snapshot')
    require(r['object']['sha256']==e['object']['sha256'],'byte-identical object')
    require(not Path(r['object']['path']).is_symlink(),'regular fresh output')
    require(r['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'caps')
    text=Path(r['log']['path']).read_text()
    require(not re.search(r'\b(?:error|warning):|sorryAx',text),'diagnostic')
    reports=[list(x) for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
    require(reports==e['axiom_reports'],'exact report content')
    for name,axioms in reports:
        require(set(re.findall(r'[A-Za-z][A-Za-z.]*',axioms))<={'propext','Classical.choice','Quot.sound'},'axioms '+name)
    r=dict(r,axiom_reports=reports,byte_identical=True)
    records.append(r)
require(sum(len(r['axiom_reports']) for r in records)==8,'eight reports')
require(shutil.disk_usage(P).free>=512*1024**2,'512MiB reserve')
out=dict(status='PASS',scope='Eight independent fresh Lean invocations; separate read-only verification corrects tuple/list normalization after the original wrapper reported failure. No compiler rerun, source edit or object mutation.',
    private=str(P),inputs=state['inputs'],original_failed_state=record(P/'PEER.json'),
    original_driver=state['driver'],verification_driver=record(__file__),records=records,
    observations=observations,final_free_bytes=shutil.disk_usage(P).free)
save(P/'VERIFIED.json',out)
print(json.dumps(dict(status='PASS',records=len(records),axiom_reports=8,observations=len(observations),packet=record(P/'VERIFIED.json')),indent=2))
