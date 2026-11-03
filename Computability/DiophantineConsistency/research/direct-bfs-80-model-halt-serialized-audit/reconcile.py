#!/usr/bin/env python3
"""Reconcile the captured BFS closure with the earlier 90 iPRA headers and chunk receipts."""
from pathlib import Path
from hashlib import sha256
import json,os
H=Path(__file__).resolve().parent;D=H.parents[1]
CAP=H/'observations/attempt01/result.json';OLD=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
MAN=D/'research/direct-bfs-lean-conjugacy-coverage-prototype/coverage-manifest-v2.json'
COV=D/'research/direct-bfs-lean-conjugacy-coverage-prototype/observations/full01'
OUT=H/'observations/reconcile01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise RuntimeError(m)
need(not OUT.exists(),'refusing overwrite')
need(sha(CAP)=='9591ab25369f57a711315fbee02bd19a360ec4aba15535dc44e85cc983a84003','capture pin')
need(sha(OLD)=='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed','old join pin')
need(sha(MAN)=='d0847a6276885e969d06cf6c2f3f64b1de1f1cfba71095e35c33393630a57392','coverage manifest pin')
a=json.loads(CAP.read_text());b=json.loads(OLD.read_text());need(a['status']=='PASS_CAPTURE' and b['status']=='PASS','previous status')
project=a['closure']['project'];old=b['post_headers']['project']
def digest(x):return None if x is None else x['sha256']
matched=[];diff=[];missing=[]
for n,row in project.items():
 if n not in old:missing.append(n);continue
 previous=old[n]
 comp={k:(digest(row['companions'][k]),digest(previous['companions'][k])) for k in row['companions']}
 if digest(row['record'])==digest(previous['record']) and all(x==y for x,y in comp.values()):matched.append(n)
 else:diff.append({'module':n,'selected_object':digest(row['record']),'prior_object':digest(previous['record']),'companion_hashes':comp})
records=json.loads(MAN.read_text())['records'];checked=[];need(len(records)==59,'bad chunk count')
for rec in records:
 n=rec['module'];p=COV/f"stage-{rec['index']:03d}"/'terminal.json';d=json.loads(p.read_text())
 need(n in project,'chunk not in selected closure '+n)
 row=project[n];need(d['accepted'] and d['exit']==0 and not d['reason'] and d['ranges']==rec['ranges'] and d['source_sha256']==rec['source_sha256'],'bad chunk receipt '+n)
 need(d['object_sha256']==digest(row['record']) and sha(row['path'])==d['object_sha256'],'chunk output differs '+n)
 need(sha(p.parent/'source.lean')==d['source_sha256'] and sha(p.parent/'stdout')==d['stdout_sha256'] and sha(p.parent/'stderr')==d['stderr_sha256'],'chunk evidence differs '+n)
 base=project.get('DirectBFSConjugacyChunk');need(base is not None and d['direct_import']['sha256']==digest(base['record']),'chunk base differs '+n)
 checked.append({'module':n,'receipt':str(p),'receipt_sha256':sha(p),'object_sha256':d['object_sha256']})
need(sha(CAP)=='9591ab25369f57a711315fbee02bd19a360ec4aba15535dc44e85cc983a84003' and sha(OLD)=='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed','input drift')
result={'status':'PASS_CAPTURE','scope':'hash comparison to captured 90 join post-header objects and companions, plus 59 retained chunk receipt checks; does not authenticate transitive package/dynamic or historical source ancestry','capture_sha256':sha(CAP),'prior_join_sha256':sha(OLD),'coverage_manifest_sha256':sha(MAN),'matched':sorted(matched),'differing':diff,'absent_from_prior':sorted(missing),'chunks':checked,'report':{'matched':len(matched),'differing':len(diff),'absent_from_prior':len(missing),'chunks_checked':len(checked)}}
OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result['report']))
