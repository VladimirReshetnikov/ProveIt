#!/usr/bin/env python3
"""Read-only bounded word-cell observation, not an atomic producer capture."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
R=ROOT/'Computability/DiophantineConsistency/research'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs={
 'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json':'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c',
 'ordinary12-ipra-bridge/compact44-word-cell-author-rebuild/observations/author/CompactWordCellClient.json':'cf620f505aa675774903049f57e45eff72fbeeb4e00316ac1bdf55c9f432af4d',
 'ordinary12-ipra-bridge/compact44-word-cell-author-rebuild/observations/author/src/DiophantineConsistency/CompactWordCellClient.lean':'7523e9d67c2e1683c1060ba561953472fbb32a6160b85083c3dfb270872579ca',
 'ordinary12-ipra-bridge/compact44-word-cell-client-plan/CompactWordCellClient-DRAFT.lean':'7523e9d67c2e1683c1060ba561953472fbb32a6160b85083c3dfb270872579ca',
 'ordinary12-ipra-bridge/compact44-word-cell-author-rebuild/observations/author/logs/CompactWordCellClient.log':'8464a94bccccf94ad0d738e3df7e7300e85447a37fe0d0701c49477b7159fb23'}
for p,h in inputs.items():assert sha(R/p)==h
f=json.loads((R/next(iter(inputs))).read_text());r=json.loads((R/list(inputs)[1]).read_text())
n='DiophantineConsistency.CompactWordCellClient';selected=f['selected_project'][n]['.olean']; obj=Path(selected['resolved']); source=Path(r['command'][5]);
assert r['exit']==0 and r['module']==n.split('.')[-1]
assert r['log_sha256']==inputs[list(inputs)[4]]
assert str(obj)==r['command'][7] and r['output'][str(obj)]['resolved']==str(obj)
assert r['output'][str(obj)]['sha256']==selected['sha256']==sha(obj)
assert sha(source)==inputs[list(inputs)[2]]
header=f['serialized_headers'][n]; assert set(header)==set(r['direct'])
direct={}
for mod,d in sorted(r['direct'].items()):
 record=d['record']; selected_import=(f['selected_project'].get(mod) or f['selected_outside'][mod])['.olean'];p=Path(d['path']);
 assert str(p.resolve())==record['resolved']==selected_import['resolved']
 assert sha(p)==record['sha256']==selected_import['sha256']
 direct[mod]={'recorded_path':str(p),'resolved':str(p.resolve()),'selected_path':selected_import['path'],'sha256':sha(p)}
for p,h in inputs.items():assert sha(R/p)==h
assert sha(source)==inputs[list(inputs)[2]] and sha(obj)==selected['sha256']
for d in direct.values():assert sha(d['resolved'])==d['sha256']
print(json.dumps({'status':'PASS','scope':'Current source, record, log and selected direct object observations; no atomic or producer-time source hash linkage, implicit companion, transitive or package ancestry claim.','inputs':inputs,'module':n,'header':header,'selected_object':selected,'command_source':str(source),'current_source_sha256':sha(source),'reported_exit':r['exit'],'reported_log_sha256':r['log_sha256'],'direct_olean':direct},sort_keys=True,indent=2))
