#!/usr/bin/env python3
"""Independent source-only audit of the original 14-variable candidate."""
import hashlib,json,re,subprocess
from pathlib import Path
D=Path(__file__).resolve().parent;V=D.parent;R=D.parents[3]
N=V/'ipra-current-native14-post172-source-survey'
B=V/'ipra-current-repaired-post172-source-survey'
O=V/'ipra-current-native14-eleven-drift-source-survey'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
paths=[Path(__file__).resolve(),N/'manifest.json',N/'dependency-inheritance-receipt.json',B/'manifest.json',B/'lean-deps-receipt.json',O/'manifest.json',O/'dependency-inheritance-receipt.json']
before={str(p):H(p) for p in paths}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
m,dep,base,lean,old,prior=(json.loads(p.read_text()) for p in paths[1:])
assert m['status']==base['status']==old['status']=='CANDIDATE_SOURCE_SNAPSHOT'
assert dep['status']==prior['status']=='PASS_DEPENDENCY_RECEIPT_COVERAGE' and lean['status']=='PASS_HEADER_DEPS'
assert len(m['sources'])==995 and set(m['sources'])==set(old['sources'])
shared=set(m['sources'])&set(base['sources']);extra=set(m['sources'])-shared
assert len(shared)==984 and len(extra)==11 and set(m['extra_order'])==extra and m['extra_order'][-1]==m['target']
seeds={'DiophantineConsistency.PRAWitnessVectors','DiophantineConsistency.PRAWitnessZFCAxioms','ZFCinPA.UniformStatement','ZFCinPA.TranslationCore'}
assert set(dep['changed'])==set(lean['rows'])==seeds and dep['changed_count']==4 and dep['unchanged_count']==991
rev={};workspace_drift=[];changed=set()
for n,row in m['sources'].items():
 p=N/'sources'/(n.replace('.','/')+'.lean');assert p.is_file() and not p.is_symlink() and H(p)==row['sha256'],n
 assert re.findall(r'^import\s+([A-Z][\w.]*)',p.read_text(),re.M)==row['imports'],n
 if H(R/row['path'])!=row['sha256']:workspace_drift.append(n)
 if row!=old['sources'][n]:changed.add(n)
 if n in shared:assert row==base['sources'][n],n
 else:assert row==old['sources'][n],n
assert changed==seeds
reachable=set();stack=[m['target']]
while stack:
 n=stack.pop()
 if n not in reachable:
  reachable.add(n);stack.extend(x for x in m['sources'][n]['imports'] if x in m['sources'])
assert reachable==set(m['sources'])
pos={n:i for i,n in enumerate(m['extra_order'])}
assert all(pos[x]<pos[n] for n in pos for x in m['sources'][n]['imports'] if x in pos)
for name,row in lean['rows'].items():
 assert hashlib.sha256(row['stdout'].encode()).hexdigest()==row['stdout_sha256']
 assert all(sum(p.endswith('/'+depname.replace('.','/')+'.olean') for p in row['stdout'].splitlines())==1 for depname in m['sources'][name]['imports'])
for receipt in (dep,prior,lean):
 for path,digest in receipt['input_sha256'].items():assert H(path)==digest,path
assert not m['workspace_drift_before'] and not m['workspace_drift_after']
assert {str(p):H(p) for p in paths}==before
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()==head
out={'status':'PASS_SOURCE_SNAPSHOT','source_count':len(m['sources']),'shared':len(shared),'extra':len(extra),'changed':sorted(changed),'workspace_drift_at_audit':sorted(workspace_drift),'input_sha256':before,'head':head,'capture_head_before':m['head_before'],'capture_head_after':m['head_after'],'scope':'Frozen source bytes and direct header coverage only; no current object-origin or proof-replay assertion.'}
p=D/'receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('PASS_SOURCE_SNAPSHOT',len(m['sources']),'sources; current workspace drift',sorted(workspace_drift))
