#!/usr/bin/env python3
"""Owned offline reconstruction of the accepted-scope source delta."""
from pathlib import Path
import hashlib, json
if not __debug__: raise SystemExit('Assertions must be enabled')
D=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
old_record=json.loads((D/'prior_current_review.json').read_text())
new_record=json.loads((D/'current/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase14/integration/current-review.json').read_text())
def scope(record, root, fallback=None):
    out={}
    for name,r in record['sources'].items():
        p=r['current'].split('/Proofs/')[1]
        assert p not in out
        q=root/p
        if not q.exists():
            assert fallback is not None
            q=fallback/p
        b=q.read_bytes();assert H(b)==r['sha256'],p
        out[p]=b
    return out
old=scope(old_record,D/'prior_sources',D/'current');new=scope(new_record,D/'current')
assert len(old)==199 and len(new)==198
changed=[];removed=[];added=[]
for p in sorted(old.keys()|new.keys()):
    a,b=old.get(p),new.get(p)
    if a==b:continue
    if a is None:added.append({'path':p,'after_bytes':len(b),'after_lines':b.count(b'\n')})
    elif b is None:removed.append({'path':p,'before_bytes':len(a),'before_lines':a.count(b'\n')})
    else:changed.append({'path':p,'before_bytes':len(a),'after_bytes':len(b),'before_lines':a.count(b'\n'),'after_lines':b.count(b'\n')})
expected=json.loads((D/'MAINTAINED_DELTA.json').read_text())
for k,v in [('changed',changed),('removed',removed),('new',added)]:
    assert {r['path']:r for r in v}=={r['path']:r for r in expected[k]},k
byte_delta=sum(map(len,new.values()))-sum(map(len,old.values()))
line_delta=sum(b.count(b'\n')for b in new.values())-sum(b.count(b'\n')for b in old.values())
assert byte_delta==expected['selected_project_source_delta_bytes']==-36327
assert line_delta==expected['selected_project_source_delta_lines']==-653
result={'status':'PASS_ACCEPTED_SCOPE_DELTA_REPLAY','base_pin':'57541fe0cfe3af62b4cb58747d8d1d7c16b338d5','pin':'6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95','prior_sources_bound':len(old),'prior_changed_sources_bundled':10,'prior_unchanged_sources_hash_reused':189,'current_sources_bound':len(new),'changed_sources':len(changed),'removed_sources':len(removed),'added_sources':len(added),'delta_lines':line_delta,'delta_bytes':byte_delta,'scope':'Accepted project sources only; excludes separate K217 changes and generators.'}
(D/'DELTA_REPLAY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
