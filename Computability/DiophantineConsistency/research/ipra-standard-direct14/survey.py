#!/usr/bin/env python3
"""Audit the recorded historical direct-square endpoint closure and drift."""
import hashlib,json
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
ROOT=D.parents[3]
TASK=D.parents[1]
SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PAIR=Path('/tmp/ipra-aq29-fresh-project-pair')
AUDIT=TASK/'reviews/fresh-project-pair-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
assert H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert H(AUDIT/'receipt.json')=='b9c77761c2944dc83b02595db874874432280903fe1c527754f0cdc858b5142e'
receipt=read(AUDIT/'receipt.json');terminal=read(AUDIT/'terminal-observation.json')
assert receipt['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' and terminal['exit_code']==0
assert terminal['receipt_sha256']==H(AUDIT/'receipt.json')
states={k:read(PAIR/k/'state.json') for k in ('author','peer')}
for k in states:
 assert states[k]['status']=='PASS' and len(states[k]['records'])==1210
 assert H(PAIR/k/'state.json')==receipt[k+'_state_sha256']
m=read(SNAP/'manifest.json');target='DiophantineConsistency.IPRASquareWitnessDirect14Native'
pending=[target];closure=set()
while pending:
 n=pending.pop()
 if n in closure or n not in m['sources']:continue
 closure.add(n);pending.extend(m['sources'][n]['imports'])
assert len(closure)==1099
before={};drift=[]
for n in sorted(closure):
 row=m['sources'][n];work=ROOT/row['workspace_path'];snap=SNAP/row['snapshot_path']
 assert work.is_file() and snap.is_file() and H(snap)==row['sha256']
 before[n]=H(work)
 if before[n]!=row['sha256']:drift.append(n)
assert len(drift)==15
names=['DiophantineConsistency.AdaptiveSquareWitnessDirect14',target]
recorded={}
for n in names:
 rr=[next(r for r in states[k]['records'] if r['module']==n) for k in ('author','peer')]
 assert all(r['exit']==0 and r['source_sha256']==m['sources'][n]['sha256'] for r in rr)
 assert rr[0]['source_sha256']==rr[1]['source_sha256'] and rr[0]['object_sha256']==rr[1]['object_sha256']
 assert all(not r['axiom_reports'] and H(r['log'])==r['log_sha256'] for r in rr)
 recorded[n]={'source_sha256':rr[0]['source_sha256'],'object_sha256':rr[0]['object_sha256'],'parent_reports':0}
assert 'DiophantineConsistency.IPRASquareWitnessDirect14NativeChecks' not in m['sources']
assert all(H(ROOT/m['sources'][n]['workspace_path'])==before[n] for n in closure)
out=D/'survey-receipt.json'
if out.exists() or out.is_symlink():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps({'status':'PASS_DIRECT14_PARENT_CLOSURE_SURVEY','target':target,
 'closure_count':len(closure),'closure':sorted(closure),'workspace_sha256':before,
 'workspace_drift':drift,'missing':[],'parent_rows':recorded,
 'parent_manifest_sha256':H(SNAP/'manifest.json'),'paired_audit_sha256':H(AUDIT/'receipt.json'),
 'scope':'Point-in-time declared project closure and recorded paired artifacts; not a current-source build, a new Lean replay, or complete dynamic/package provenance.'},indent=2,sort_keys=True)+'\n')
print('PASS_DIRECT14_PARENT_CLOSURE_SURVEY',len(closure),len(drift),H(out))
