"""Owned, data-only offline recheck of the pinned review artifacts. Executes no received code."""
from pathlib import Path
import hashlib,json,tarfile,collections,sys
if sys.flags.optimize:
 raise RuntimeError("Run without Python optimization; this audit requires active assertions.")
D=Path(__file__).resolve().parent; B=D/'current'; V=B/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification'; H=lambda b:hashlib.sha256(b).hexdigest()
binding=json.loads((D/'CURRENT_BINDING.json').read_text()); source_rows=[]
recorded=json.loads((V/'phase14/integration/current-review.json').read_text())['sources']
assert set(recorded)=={r['module'] for r in binding['current_source_rows']}
assert len(recorded)==len(binding['current_source_rows'])==198
for r in binding['current_source_rows']:
 upstream=recorded[r['module']]; assert r['path']==upstream['current'].split('/Proofs/')[1]
 h=H((B/r['path']).read_bytes());assert h==upstream['sha256']==r['recorded_sha256']==r['sha256'],r['path'];source_rows.append(r['path'])
archives=[]
for phase in ['phase13','phase14']:
 p=V/phase/'lean'; index=json.loads((p/'index.json').read_text()); result=json.loads((p/'result.json').read_text()); raw=(p/'execution.tar.gz').read_bytes(); assert H(raw)==result['archive_sha256']; assert H((p/'index.json').read_bytes())==result['index_sha256']
 with tarfile.open(p/'execution.tar.gz') as t:
  for name,r in index.items():
   b=t.extractfile(name).read();assert H(b)==r['sha256'] and len(b)==r['bytes'],name
  archives.append({'phase':phase,'indexed_members':len(index),'matching_members':len(index),'archive_sha256':H(raw)})
# Retired paths are checked against complete current directory data, not the capped Contents list.
lean_tree=json.loads((D/'LEAN_TREE.json').read_text()); assert lean_tree['truncated'] is False
assert 'KProfileTC.lean' not in {r['path'] for r in lean_tree['tree']}
formal_names={r['name'] for r in json.loads((D/'FORMAL_DIR.json').read_text())}
assert 'generate_profile_tc.py' not in formal_names and 'generate_enumdom.py' not in formal_names
# Scope checks against accepted ledgers; original failed client remains excluded.
with tarfile.open(V/'phase14/lean/execution.tar.gz') as t:
 read=lambda n:json.loads(t.extractfile(n).read()); ledgers={s:read(s+'/completed.json') for s in ['execution','compatibility']}
 scopes={}
 for name,rows in ledgers.items():
  assert all(r['status']=='PASS' for r in rows.values());scopes[name]={'providers':len(rows),'origins':dict(collections.Counter(r['origin'] for r in rows.values()))}
 accepted=ledgers['execution']['ProfileTC14Api']; failed=read('failed-primary/attempts/066-ProfileTC14Api/record.json');fixed=read('execution/fresh/ProfileTC14Api/record.json');assert failed['status']=='FAIL' and failed['exit_code']==1 and failed['object_sha256'] is None;assert fixed['status']=='PASS' and fixed['exit_code']==0;assert accepted['source_sha256']==fixed['source_sha256']!=failed['source_sha256'];assert all('sorryAx' not in a for _,a in fixed['reports'])
 audits=[]
 for module in ['K215Audit','EndpointAudit215']:
  j=read('execution/audits/'+module+'.json'); log=t.extractfile('execution/audits/'+module+'.log').read();assert H(log)==j['log_sha256'];assert j['exit_code']==0 and j['status']=='PASS';assert b'sorryAx' not in log and b'warning:' not in log;audits.append({'module':module,'reports':j['named_reports'],'exit_code':j['exit_code'],'warnings':0,'source_sha256':j['source_sha256']})
result={'status':'PASS_OWNED_DATA_ONLY_REPLAY','pin':binding['pin'],'current_source_matches':len(source_rows),'archives':archives,'selected_ledgers':scopes,'failed_client_excluded':True,'endpoint_audits':audits,'scope':'Source bytes, archived member hashes, selected ledger status and endpoint raw-log checks only; not compilation, live-object validity, full inherited provenance replay, or independent proof verification.'}
(D/'OWNED_REPLAY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
