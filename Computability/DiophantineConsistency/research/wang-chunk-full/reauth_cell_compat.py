"""Read-only complete source/provider reauthentication of a CellWindow build."""
from pathlib import Path
import hashlib,json,os,shutil,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');P=Path('/tmp/adaptive13-cell-root-parent-wnvsel13');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');D=Path(os.environ.get('CELL_COMPAT_BUILD','/tmp/adaptive13-cell-compat-guarded-mfrskqz1'));S={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver'};Q=Path('/tmp/adaptive-wang-chunk-full-src/DiophantineConsistency')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ds=read(D/'state.json');ps=read(P/'state.json');bs=read(B/'state.json');C=Path(ds['compat_provider']);cs=read(C/'state.json');chunk=Path(cs['chunk_provider']);ck=read(chunk/'state.json');g=read(B/'guards.json');pr=read(B/'providers.json');selected=read(D/'providers.json');orig=read(P/'providers.json');assert ds['status']==bs['status']==cs['status']==ck['status']=='PASS';assert len(ds['records'])==6 and len(ds['completed_prefix'])==36 and len(ps['order'])==46
assert sha(P/'state.json')==ds['parent_state_sha256'] and sha(P/'providers.json')==ds['parent_provider_sha256'] and sha(B/'state.json')==ds['current_base_state_sha256'] and sha(D/'providers.json')==ds['providers_sha256'] and sha(C/'state.json')==ds['compat_state_sha256'];assert sha(B/'guards.json')==bs['guards_sha256']==cs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256']==cs['providers_sha256'] and sha(chunk/'state.json')==cs['chunk_state_sha256'];dh=sha(D/'state.json')
def auth():
 if not (sha(D/'state.json')==dh and sha(P/'state.json')==ds['parent_state_sha256'] and sha(P/'providers.json')==ds['parent_provider_sha256'] and sha(B/'state.json')==ds['current_base_state_sha256'] and sha(D/'providers.json')==ds['providers_sha256'] and sha(C/'state.json')==ds['compat_state_sha256'] and sha(C/'lib/DiophantineConsistency/ArithmeticWangTable.olean')==cs['object_sha256'] and sha(chunk/'state.json')==cs['chunk_state_sha256'] and sha(B/'guards.json')==bs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256']):return False
 if not all(sha(p)==h for p,h in g.items()) or not all(sha(x['path'])==x['sha256'] for x in pr.values()) or not all(sha(p)==h for p,h in selected.items()) or not all(sha(p)==h for p,h in orig.items()):return False
 for key in ps['order']:
  ns,n=key.split('.',1);src=S[ns]/(n+'.lean');snap=P/'logs'/ns/(n+'.lean')
  if not sha(src)==sha(snap)==ps['snapshots'][key]:return False
 for row in ds['completed_prefix']:
  ns,n=row['namespace'],row['name'];src=S[ns]/(n+'.lean');obj=P/'lib'/ns/(n+'.olean');log=P/'logs'/ns/(n+'.log');tim=P/'logs'/ns/(n+'.time')
  if not (row['exit']==0 and sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(log)==row['log_sha256'] and sha(tim)==row['time_sha256']):return False
 for row in ds['records']:
  ns,n=row['namespace'],row['name'];src=S[ns]/(n+'.lean');obj=D/'lib'/ns/(n+'.olean');log=D/'logs'/ns/(n+'.log');tim=D/'logs'/ns/(n+'.time');snap=D/'logs'/ns/(n+'.lean')
  if not (row['exit']==0 and sha(src)==sha(snap)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(log)==row['log_sha256'] and sha(tim)==row['time_sha256']):return False
 return all(sha(Q/(x['name']+'.lean'))==x['source_sha256'] and sha(chunk/'lib/DiophantineConsistency'/(x['name']+'.olean'))==x['object_sha256'] and sha(chunk/'logs'/(x['name']+'.log'))==x['log_sha256'] for x in ck['records'])
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-cell-compat-reauth-'));shutil.copyfile(__file__,w/'driver.py');state={'status':'RUNNING','private':str(w),'build':str(D),'build_state_sha256':dh,'source_snapshot_count':46,'prefix_count':36,'built_count':6,'guards_count':len(g),'base_provider_count':len(pr),'selected_count':len(selected),'scope':'Read-only complete post-build source, object, log and provider reauthentication; private split compatibility remains snapshot-qualified and is not canonical integration.'};save=lambda:(w/'state.json').write_text(json.dumps(state,indent=2)+'\n');save();print('PRIVATE',w,flush=True)
try:
 assert auth();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
