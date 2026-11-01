#!/usr/bin/env python3
"""Audit the refreshed 14-variable source capture, without object claims."""
import hashlib
import json
from pathlib import Path

D=Path(__file__).resolve().parent
V=D.parent
R=D.parents[3]
F=V/'ipra-current-native14-six-drift-source-survey'
S=V/'ipra-current-repaired-six-drift-source-survey'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=json.loads((F/'manifest.json').read_text())
parent=json.loads((S/'manifest.json').read_text())
assert m['status']=='CANDIDATE_SOURCE_SNAPSHOT'
assert not m['workspace_drift_before'] and not m['workspace_drift_after']
assert m['head_before']==m['head_after'] and len(m['sources'])==995
shared=set(m['sources']) & set(parent['sources'])
extra=set(m['sources'])-set(parent['sources'])
assert len(shared)==984 and len(extra)==11
for name,row in m['sources'].items():
    file=F/'sources'/(name.replace('.', '/')+'.lean')
    assert file.is_file() and not file.is_symlink() and file.resolve()==file.absolute()
    assert sha(file)==row['sha256'] and sha(R/row['path'])==row['sha256'],name
    if name in shared:
        assert row['sha256']==parent['sources'][name]['sha256']
        assert row['imports']==parent['sources'][name]['imports']
order=m['extra_order'];index={n:i for i,n in enumerate(order)}
assert set(index)==extra and len(index)==11 and order[-1]==m['target']
assert all(index[d]<index[n] for n in order for d in m['sources'][n]['imports'] if d in index)
assert set(m['external'])<=set(parent['external'])
report={'status':'PASS_SOURCE_SNAPSHOT','sources':len(m['sources']),
        'shared':len(shared),'additional':len(extra),
        'manifest_sha256':sha(F/'manifest.json'),'auditor_sha256':sha(__file__),
        'scope':'Source bytes, shared hashes and recorded ordering only; object origins, dependency parser and endpoint replay remain separate.'}
(D/'receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print('PASS_SOURCE_SNAPSHOT',len(m['sources']),'sources,',len(shared),'shared,',len(extra),'additional')
