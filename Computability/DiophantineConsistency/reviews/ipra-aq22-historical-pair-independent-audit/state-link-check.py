#!/usr/bin/env python3
"""Check sibling build-state links to the pinned preparation and driver."""
import hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;RUN=Path('/tmp/ipra-aq22-historical-paired-run-02');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
paths=[Path(__file__),RUN/'prepared/preparation.json',RUN/'pair/pair-state.json']+[RUN/'prepared'/x/'rebuild-state.json' for x in ('author','peer')]
before={str(p.resolve()):H(p) for p in paths};prep=J(paths[1]);pair=J(paths[2]);rows={}
for label in ('author','peer'):
 p=RUN/'prepared'/label/'rebuild-state.json';state=J(p);row=next(r for r in pair['runs'] if r['label']==label)
 assert H(p)==row['builder_state_sha256']==pair['comparison'][label+'_state_sha256']
 assert state['status']=='PASS' and state['sibling']==label and state['source_basis']=='HISTORICAL_PARENT'
 for key in ('old_snapshot_sha256','new_snapshot_sha256','parent_pair_sha256'):
  assert state[key]==prep[key],(label,key)
 assert state['preparation_sha256']==H(paths[1])==pair['preparation_sha256']
 assert state['driver_sha256']==pair['driver_sha256']
 assert state['expected_axiom_reports']==3
 rows[label]={'state_sha256':H(p),'workspace_head':state['workspace_head']}
assert {str(p.resolve()):H(p) for p in paths}==before
result={'status':'PASS_AQ22_PAIRED_STATE_LINKS','inputs_sha256':before,'siblings':rows,'scope':'State-link metadata only; no source or object hashing, Lean replay or current-source claim.'}
out=HERE/'state-link-receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
