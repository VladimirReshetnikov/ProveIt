#!/usr/bin/env python3
"""Bounded read-only producer extension. No Lean or build."""
import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2]; D=Path(__file__).resolve().parent
pinned=json.loads((D/'pins.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in pinned.items():
 q=Path(p) if p.startswith('/') else R/p
 assert sha(q)==h,p
previous=json.loads((R/'research/adaptive87-peer-recorded-producer-trace/receipt.json').read_text())
origin=json.loads((R/'reviews/ipra-frozen-repair-plan-v2-source-origin-audit/source-nodes.json').read_text())
providerroots=['/tmp/ipra-bounded-induction-postmerge-wgkld2w0','/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt','/tmp/pra14-full-transitive-g3ull6n_']
records={}
for owner in providerroots:
 state=json.loads(Path(owner+'/state.json').read_text());assert state['status']=='PASS'
 for row in state['records']:
  name=row.get('module',row.get('name'))
  if not name.startswith('DiophantineConsistency.'):name='DiophantineConsistency.'+name
  deps=row['dependency_hashes'] if 'dependency_hashes' in row else {k:v['sha256'] for k,v in row['direct_imports'].items()}
  records[(owner,name,row['object_sha256'])]=(row,deps)
root=Path('/tmp/nine-ipra-guarded-peer-20261102-a/lib')
def current(n):
 p=root/Path(n.replace('.','/')+'.olean')
 if not p.is_file():return None
 return {'path':str(p.resolve()),'sha256':sha(p)}
stack=previous['missing_record'][:]; original=set(stack);done={};edges=[];unmatched=[];external=set();into_previous=set()
while stack:
 n=stack.pop()
 if n in done:continue
 if n not in original and n in previous['seen']:
  v=current(n);assert v and v['path']==previous['seen'][n]['path'] and v['sha256']==previous['seen'][n]['sha256'];into_previous.add(n);continue
 v=current(n)
 if not v:unmatched.append({'module':n,'reason':'missing selected object'});done[n]=None;continue
 owner=v['path'].split('/lib/')[0]
 rec=records.get((owner,n,v['sha256']))
 if not rec:unmatched.append({'module':n,'reason':'no matching selected-owner row','owner':owner,'sha256':v['sha256']});done[n]=v;continue
 row,deps=rec;assert row['exit']==0
 key=n+'|'+v['sha256']+'|'+v['path']; old=origin.get(key)
 source=None
 if old:
  assert old['owner']==owner and old['provider_state_sha256']==sha(owner+'/state.json')
  assert sha(old['source_path'])==old['source_sha256'] and sha(old['log_path'])==old['log_sha256']
  source={'source_path':old['source_path'],'source_sha256':old['source_sha256'],'log_sha256':old['log_sha256']}
  if 'source_sha256' in row:assert row['source_sha256']==old['source_sha256']
 done[n]=dict(v,owner=owner,source_origin=source)
 if n in original:assert source is not None,n
 for dep,h in deps.items():
  if not dep.startswith('DiophantineConsistency.'):external.add(dep);continue
  got=current(dep);edges.append({'from':n,'to':dep,'recorded':h,'selected':got and got['sha256'],'matches':got is not None and got['sha256']==h})
  if got and got['sha256']==h:stack.append(dep)
miss=[e for e in edges if not e['matches']]
print(json.dumps({'initial_boundaries':sorted(original),'nodes':done,'edges':edges,'project_edge_mismatches':miss,'unmatched':unmatched,'into_previous':sorted(into_previous),'external_names':sorted(external),'scope':'selected physical-owner rows; source snapshots and logs when prior origin inventory provides them; no package/dynamic completeness'},indent=2,sort_keys=True))
