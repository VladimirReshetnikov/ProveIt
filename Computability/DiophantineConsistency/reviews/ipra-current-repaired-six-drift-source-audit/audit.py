#!/usr/bin/env python3
"""Independently audit a source-only successor snapshot, not object ancestry."""
import hashlib
import json
from pathlib import Path

D=Path(__file__).resolve().parent
V=D.parent
R=D.parents[3]
N=V/'ipra-current-repaired-six-drift-source-survey'
O=V/'ipra-current-repaired-survey'
P=V/'ipra-current-repaired-postmerge-preliminary-v3'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
new=json.loads((N/'manifest.json').read_text())
old=json.loads((O/'manifest.json').read_text())
pre=json.loads((P/'manifest.json').read_text())
assert new['status']=='CANDIDATE_SOURCE_SNAPSHOT'
assert not new['workspace_drift_before'] and not new['workspace_drift_after']
assert new['head_before']==new['head_after'] and new['order']==pre['source_topological_order']
assert set(new['sources'])==set(old['sources']) and len(new['sources'])==1099
drift=set()
for name,row in new['sources'].items():
    path=N/'sources'/(name.replace('.','/')+'.lean')
    assert path.is_file() and not path.is_symlink() and path.resolve()==path.absolute()
    assert sha(path)==row['sha256'] and sha(R/row['path'])==row['sha256'], name
    assert row['imports']==old['sources'][name]['imports'], name
    if row['sha256']!=old['sources'][name]['sha256']:drift.add(name)
assert drift==set(pre['drift']) and len(drift)==6
assert len(new['order'])==107 and set(new['order'])==set(pre['impacted'])
index={name:i for i,name in enumerate(new['order'])}
assert all(index[d]<index[n] for n in index for d in new['sources'][n]['imports'] if d in index)
assert sha(N/'manifest.json')=='a3a165cd4243d7df56c08a1a8c3a843c288e8736048682099e6966dda02d0e69'
report={'status':'PASS_SOURCE_SNAPSHOT','sources':len(new['sources']),'changed':sorted(drift),
        'planned_modules':len(index),'manifest_sha256':sha(N/'manifest.json'),
        'auditor_sha256':sha(__file__), 'scope':'Source bytes and captured ordering only; '
        'no Lean dependency parser, object-origin or completed successor replay audit.'}
(D/'receipt.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
print('PASS_SOURCE_SNAPSHOT',len(new['sources']),'sources,',len(drift),'changed,',len(index),'planned')
