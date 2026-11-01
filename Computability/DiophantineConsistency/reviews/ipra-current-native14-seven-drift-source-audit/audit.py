#!/usr/bin/env python3
"""Independently audit the 14-variable seven-drift source candidate only."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
D=Path(__file__).resolve().parent
V=D.parent
R=D.parents[3]
N=V/'ipra-current-native14-seven-drift-source-survey'
B=V/'ipra-current-repaired-seven-drift-source-survey'
O=V/'ipra-current-native14-six-drift-source-survey'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs=[Path(__file__).resolve(),N/'manifest.json',N/'dependency-inheritance-receipt.json',B/'manifest.json',O/'manifest.json']
before={str(p):H(p) for p in inputs}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
m,b,o=(json.loads(p.read_text()) for p in (N/'manifest.json',B/'manifest.json',O/'manifest.json'))
assert m['status']==b['status']==o['status']=='CANDIDATE_SOURCE_SNAPSHOT'
assert m['head_before']==m['head_after'] and not m['workspace_drift_before'] and not m['workspace_drift_after']
assert len(m['sources'])==995 and set(m['sources'])==set(o['sources']) and m['external']==o['external']
shared=set(m['sources'])&set(b['sources']);extra=set(m['sources'])-set(b['sources'])
assert len(shared)==984 and len(extra)==11 and set(m['extra_order'])==extra and len(m['extra_order'])==11
changed=[]
for name,row in m['sources'].items():
    p=N/'sources'/(name.replace('.','/')+'.lean')
    assert p.is_file() and not p.is_symlink() and H(p)==row['sha256'] and H(R/row['path'])==row['sha256'],name
    assert re.findall(r'^import\s+([A-Z][\w.]*)',p.read_text(),re.M)==row['imports'],name
    assert row==(b['sources'][name] if name in shared else o['sources'][name]),name
    if row!=o['sources'][name]:changed.append(name)
assert changed==['ZFCinPA.SeparationKernel']
assert set(m['sources'][changed[0]]['imports'])-set(o['sources'][changed[0]]['imports'])=={'ZFCinPA.ModelCodedSchemaAxioms'}
pos={name:i for i,name in enumerate(m['extra_order'])}
assert all(pos[dep]<pos[name] for name in pos for dep in m['sources'][name]['imports'] if dep in pos)
assert m['extra_order'][-1]==m['target']
seen=set();stack=[m['target']]
while stack:
    name=stack.pop()
    if name not in seen:
        seen.add(name);stack.extend(dep for dep in m['sources'][name]['imports'] if dep in m['sources'])
assert seen==set(m['sources'])
r=json.loads((N/'dependency-inheritance-receipt.json').read_text())
assert r['status']=='PASS_DEPENDENCY_RECEIPT_COVERAGE'
assert H(N/'manifest.json')=='596734fad33099d822d9a80b07ab6e9b26f443d04bff4f40e3c83fec9041a22f'
assert H(N/'dependency-inheritance-receipt.json')=='e625d1a684b6589dd34017d66978f6c1751cedfee88e4240ecfbdffbf3077166'
for path,h in r['input_sha256'].items():assert H(path)==h,path
assert {str(p):H(p) for p in inputs}==before
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()==head
out={'status':'PASS_SOURCE_SNAPSHOT','sources':len(m['sources']),'shared':len(shared),'extra':len(extra),'changed':changed,
     'input_sha256':before,'head':head,'scope':'Frozen source bytes, source headers, graph closure, extra ordering and recorded dependency-receipt input hashes only; no object or replay authentication.'}
p=D/'receipt.json';assert not p.exists();p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
print('PASS_SOURCE_SNAPSHOT',len(m['sources']),'sources;',len(shared),'shared;',len(extra),'additional')
