"""Read-only current-source/provenance audit of the reduced-zero provider."""
from pathlib import Path
import hashlib,json,os,shutil,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');D=Path('/tmp/adaptive-construction-reduced-zero-u6gt_026');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());bs=read(B/'state.json');ds=read(D/'state.json');g=read(B/'guards.json');canonical=read(B/'providers.json');assert bs['status']==ds['status']=='PASS' and sha(B/'guards.json')==bs['guards_sha256']==ds['canonical_guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and sha(B/'state.json')==ds['canonical_state_sha256']
base={f.relative_to(B/'lib') for f in (B/'lib').rglob('*.olean') if f.is_file()};reduced={f.relative_to(D/'lib') for f in (D/'lib').rglob('*.olean') if f.is_file()};extras=sorted(reduced-base);assert len(base)==367 and len(extras)==40 and not base-reduced
roots={}
for rel in extras:
 p=(D/'lib'/rel).resolve();root=p.parents[2];assert root.parent==Path('/tmp');roots[str(root)]=None
records={};providers={};statehash={};providerhash={}
for rp in sorted(roots):
 p=Path(rp);st=read(p/'state.json');assert st['status']=='PASS';statehash[rp]=sha(p/'state.json');providerhash[rp]=sha(p/'providers.json');assert providerhash[rp]==st['providers_sha256']
 for row in read(p/'providers.json'):
  q=Path(row['path']).resolve();h=row['sha256'];assert q not in providers or providers[q]==h;providers[q]=h
 for row in st['records']:
  assert row['exit']==0;n=row['name'];src=S/(n+'.lean');obj=p/'lib/DiophantineConsistency'/(n+'.olean');log=p/'logs'/(n+'.log');assert sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(log)==row['log_sha256'];records[str(obj.resolve())]={'source':str(src),'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'log':str(log),'log_sha256':row['log_sha256'],'root':rp}
for rel in extras:
 obj=(D/'lib'/rel).resolve();assert str(obj) in records and sha(obj)==records[str(obj)]['object_sha256']
def auth():
 return (sha(B/'state.json')==ds['canonical_state_sha256'] and sha(B/'guards.json')==bs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and all(sha(p)==h for p,h in g.items()) and all(sha(x['path'])==x['sha256'] for x in canonical.values()) and all(sha(Path(p)/'state.json')==h and sha(Path(p)/'providers.json')==providerhash[p] for p,h in statehash.items()) and all(sha(p)==h for p,h in providers.items()) and all(sha(x['source'])==x['source_sha256'] and sha(p)==x['object_sha256'] and sha(x['log'])==x['log_sha256'] for p,x in records.items()))
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-reduced-provider-audit-'));shutil.copyfile(__file__,w/'driver.py');state={'status':'RUNNING','private':str(w),'base':str(B),'reduced':str(D),'guards_sha256':bs['guards_sha256'],'canonical_providers_sha256':bs['providers_sha256'],'record_provider_count':len(roots),'provider_object_count':len(providers),'scope':'Read-only source/object/log and inherited-provider audit of the reduced-zero extras; no combined overlay, Assembly result, or HA claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
try:
 overlap={str(rel):{'base':sha(B/'lib'/rel),'reduced':sha(D/'lib'/rel)} for rel in sorted(base)};assert all(x['base']==x['reduced'] for x in overlap.values());result={'base_count':len(base),'extra_count':len(extras),'provider_roots':statehash,'provider_manifests':providerhash,'records':records,'extras':{str(rel):str((D/'lib'/rel).resolve()) for rel in extras},'overlap':overlap};(w/'result.json').write_text(json.dumps(result,indent=2)+'\n');state['result_sha256']=sha(w/'result.json');assert auth();state['status']='PASS';save();print('PASS',w,'base',len(base),'extras',len(extras),'roots',len(roots),'provider objects',len(providers),flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
