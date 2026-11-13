#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];repo=D.parents[1];p=D/'research/current14-coherent-extension-runner';a=p/'attempt01';out=Path('/tmp/current14-coherent490-rebuild-20261110');sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_bytes());assert o['outer_session']==64963 and o['outer_exit_code']==1 and o['status']=='FAILED' and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_bytes());plan=json.loads((p/'plan.json').read_bytes());assert s['status']=='FAILED' and s['failure']==o['failure']=="Refusal('compile failed BusyBeaver.ZFC.KSource215Data')" and s['runner_sha256']==sha(p/'run.py')=='7645019eb1aebe3c89b2db585f059625f8d211005f1a0eec08f8732f2a2f55a3' and s['monitor_sha256']==sha(p/'monitor.py') and s['plan_sha256']==sha(p/'plan.json') and len(plan['entries'])==490 and len(s['rows'])==7
base=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_bytes());assert s['base_state_sha256']==sha('/tmp/current14-standard-fresh-build-20261104/state.json');base_rows={r['module']:r for r in base['records']};assert len(base_rows)==1000 and len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
# All planned source snapshots and audit client were created before compilation.
for e in plan['entries']:
 q=out/'src'/(e['module'].replace('.','/')+'.lean');assert q.is_file() and sha(q)==e['source_sha256'] and sha(repo/e['source'])==e['source_sha256']
assert sha(out/'src/DiophantineConsistency/Current14CoherentAudit.lean')==sha(p/'Current14CoherentAudit.lean')
completed={}
for i,(r,e) in enumerate(zip(s['rows'],plan['entries'])):
 n=r['module'];assert n==e['module'] and r['source_sha256']==e['source_sha256']
 for ph in ('deps','compile'):
  x=r[ph];log=Path(x['log']);name=log.name;assert sha(log)==sha(a/'logs'/name)==x['log_sha256']==o['captured_logs'][name] and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['disk_floor_bytes']==5100000000 and x['timeout_seconds']<=180 and x['min_disk_free_bytes']>5100000000 and x['min_host_available_bytes']>=10*1024**3 and x['peak_session_rss_bytes']<4*1024**3
  assert x['exit']==(1 if i==6 and ph=='compile' else 0)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 for dep,v in r['dependencies'].items():
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'] and r['direct_guard'][str(q)]=={'realpath':v['realpath'],'sha256':v['sha256']}
  if dep in completed:assert v['sha256']==completed[dep]
  elif dep in base_rows:assert v['sha256']==base_rows[dep]['object_sha256']
  else:assert dep in plan['external_direct'] and v['sha256']==plan['external_direct'][dep]['sha256'] and v['realpath']==plan['external_direct'][dep]['realpath']
 if i<6:
  q=out/'lib'/(n.replace('.','/')+'.olean');assert q.is_file() and not q.is_symlink() and sha(q)==r['object_sha256'];completed[n]=r['object_sha256']
  for path,v in r['output_guard'].items():
   z=Path(path)
   if v is None:assert not os.path.lexists(z)
   else:assert z.is_file() and not z.is_symlink() and str(z.resolve())==v['realpath'] and sha(z)==v['sha256']
  log=(a/'logs'/Path(r['compile']['log']).name).read_text();assert all(t not in log for t in ('error:','sorryAx'))
 else:
  assert n=='BusyBeaver.ZFC.KSource215Data' and 'object_sha256' not in r and not (out/'lib/BusyBeaver/ZFC/KSource215Data.olean').exists();log=(a/'logs'/Path(r['compile']['log']).name).read_text();assert 'error: Tactic `decide` failed' in log and '(kernel) excessive memory consumption detected' in log and 'stop_reason' in r['compile'] and r['compile']['stop_reason'] is None
assert len(completed)==6 and len(o['captured_logs'])==14 and not (out/'lib/DiophantineConsistency/Current14CoherentAudit.olean').exists() and s['elapsed_seconds']==o['elapsed_seconds']
print(json.dumps({'status':'PASS_INDEPENDENT_FAILURE_AUDIT','outer_session':64963,'successful_stages':6,'failed_stage':'BusyBeaver.ZFC.KSource215Data','lean_exit':1,'monitor_stop_reason':None,'sampled_peak_rss_bytes':s['rows'][-1]['compile']['peak_session_rss_bytes'],'scope':'FAILED run, six successful stages and their direct guards; no complete rebuild/client/postflight or new theorem'},indent=2))
