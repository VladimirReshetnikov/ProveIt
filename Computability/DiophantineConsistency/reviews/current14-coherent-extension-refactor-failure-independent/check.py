from pathlib import Path
import hashlib,json,subprocess,sys,re
root=Path(__file__).resolve().parents[2];p=root/'research/current14-coherent-extension-refactor-runner';a=p/'attempt01';live=Path('/tmp/current14-coherent490-refactor-rebuild-20261110')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['status']=='FAILED' and o['outer_session']==99055 and o['outer_exit_code']==1 and len(o['captured_logs'])==70
assert sha(a/'state.json')==o['state_sha256']=='4cfcb4a10ae4f49d853517ee542b8b9412150c4a27c3c433fee68612c5a30242'
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==35 and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='aa50f07d5dc350d30e66c45539627df66d38a187111875d604fe27924fa0463a';assert s['plan_sha256']==sha(p/'plan.json') and s['monitor_sha256']==sha(p/'monitor.py')
plan=json.loads((p/'plan.json').read_text());entries=plan['entries'];assert len(entries)==508
for e in entries:
 name=e['module'].replace('.','/');assert sha(root.parents[1]/e['source'])==sha(live/'src'/f'{name}.lean')==e['source_sha256']
client=p/'Current14CoherentAudit.lean';assert sha(client)==sha(live/'src/DiophantineConsistency/Current14CoherentAudit.lean')
prior={};totalguards=0
for i,(e,r) in enumerate(zip(entries,s['rows'])):
 n=e['module'];name=n.replace('.','/');assert n==r['module'] and e['source_sha256']==r['source_sha256'];assert set(r['dependencies'])==set(e['imports'])|{'Init'}
 for k in ('deps','compile'):
  v=r[k];q=Path(v['log']);assert sha(q)==sha(a/'logs'/q.name)==v['log_sha256']==o['captured_logs'][q.name];assert v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids']
  assert v['peak_session_rss_bytes']<v['rss_limit_bytes'] and v['min_disk_free_bytes']>v['disk_floor_bytes'] and v['min_host_available_bytes']>=v['host_floor_bytes']
  assert v['exit']==(1 if i==34 and k=='compile' else 0)
 for dep,v in r['dependencies'].items():
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  if dep in prior:assert v==prior[dep]
  elif dep=='Init':assert v['sha256']==plan['external_direct']['Init']['sha256']
  else:
   b=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text());base={x['module']:x for x in b['records']}
   if dep in base:assert v['sha256']==base[dep]['object_sha256'] and v['realpath'].startswith('/tmp/current14-standard-fresh-build-20261104/lib/')
   else:assert dep in plan['external_direct'] and v['sha256']==plan['external_direct'][dep]['sha256'] and v['realpath']==plan['external_direct'][dep]['realpath']
 for guard in (r['direct_guard'],r.get('output_guard',{})):
  for path,v in guard.items():
   totalguards+=1;q=Path(path)
   if v is None:assert not q.exists() and not q.is_symlink()
   else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 obj=live/'lib'/f'{name}.olean'
 if i<34:assert sha(obj)==r['object_sha256'];prior[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':r['object_sha256']}
 else:assert n=='BusyBeaver.ZFC.KSource215FwdCheck09' and not obj.exists() and 'object_sha256' not in r
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
log=(a/'logs'/Path(s['rows'][-1]['compile']['log']).name).read_text();assert 'Tactic `decide` failed' in log and '(kernel) excessive memory consumption detected' in log
assert s['failure']=="Refusal('compile failed BusyBeaver.ZFC.KSource215FwdCheck09')"
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-compatibility-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_INDEPENDENT_FAILURE_AUDIT','outer_session':99055,'outer_exit':1,'successful_stages':34,'failed_stage':'BusyBeaver.ZFC.KSource215FwdCheck09','failed_child_exit':1,'monitor_stop':None,'peak_sampled_rss_bytes':s['rows'][-1]['compile']['peak_session_rss_bytes'],'guard_observations':totalguards,'scope':'Kernel memory failure, no failed-stage object, no coherent endpoint or postflight'},indent=2))
