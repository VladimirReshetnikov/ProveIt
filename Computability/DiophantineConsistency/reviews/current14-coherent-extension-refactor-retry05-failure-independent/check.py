from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-coherent-extension-refactor-retry05-runner';a=p/'attempt01';live=Path('/tmp/current14-coherent490-refactor-retry05-20261110');cache={}
def sha(p):
 p=Path(p);st=p.stat();key=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
 if key not in cache:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
  st=p.stat();assert (st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)==key;cache[key]=h.hexdigest()
 return cache[key]
o=json.loads((a/'outer-result.json').read_text());assert o['status']=='FAILED' and o['outer_session']==3354 and o['outer_exit_code']==1 and len(o['captured_logs'])==478
assert sha(a/'state.json')==o['state_sha256']=='8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="Refusal('disk_floor')" and len(s['rows'])==240 and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='f025f9fdf7ec59762faab7d135bed4bff50fe841f08397c0d126f83236d3e84e' and s['plan_sha256']==sha(p/'plan.json') and s['monitor_sha256']==sha(p/'monitor.py')
plan=json.loads((p/'plan.json').read_text());entries=plan['entries'];assert len(entries)==529
for e in entries:
 name=e['module'].replace('.','/');assert sha(root.parents[1]/e['source'])==sha(live/'src'/f'{name}.lean')==e['source_sha256']
client=p/'Current14CoherentAudit.lean';assert sha(client)==sha(live/'src/DiophantineConsistency/Current14CoherentAudit.lean')
base={x['module']:x for x in json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text())['records']};prior={};guards=0
for e,r in zip(entries,s['rows'][:239]):
 n=e['module'];name=n.replace('.','/');assert n==r['module'] and e['source_sha256']==r['source_sha256'] and set(r['dependencies'])==set(e['imports'])|{'Init'}
 for k in ('deps','compile'):
  v=r[k];q=Path(v['log']);assert sha(q)==sha(a/'logs'/q.name)==v['log_sha256']==o['captured_logs'][q.name];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert v['peak_session_rss_bytes']<v['rss_limit_bytes'] and v['min_disk_free_bytes']>v['disk_floor_bytes'] and v['min_host_available_bytes']>=v['host_floor_bytes']
 for dep,v in r['dependencies'].items():
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  if dep in prior:assert v==prior[dep]
  elif dep=='Init':assert v['sha256']==plan['external_direct']['Init']['sha256']
  elif dep in base:assert v['sha256']==base[dep]['object_sha256'] and v['realpath'].startswith('/tmp/current14-standard-fresh-build-20261104/lib/')
  else:assert dep in plan['external_direct'] and v['sha256']==plan['external_direct'][dep]['sha256'] and v['realpath']==plan['external_direct'][dep]['realpath']
 for guard in (r['direct_guard'],r['output_guard']):
  for path,v in guard.items():
   guards+=1;q=Path(path)
   if v is None:assert not q.exists() and not q.is_symlink()
   else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 obj=live/'lib'/f'{name}.olean';assert sha(obj)==r['object_sha256'];prior[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':r['object_sha256']}
last=s['rows'][-1];e=entries[239];assert last['module']==e['module']=='DiophantineConsistency.Sign17KWeightAggregateProbe' and last['source_sha256']==e['source_sha256'] and 'deps' not in last and 'compile' not in last and 'object_sha256' not in last
obj=live/'lib'/(last['module'].replace('.','/')+'.olean');assert not obj.exists();assert not list((live/'logs').glob('239-*'))
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
last_sample=s['rows'][238]['compile']['min_disk_free_bytes'];assert last_sample==5104041984
print(json.dumps({'status':'PASS_INDEPENDENT_STOP_AUDIT','outer_session':3354,'outer_exit':1,'successful_stages':239,'next_stage':last['module'],'next_child_started':False,'guard_observations':guards,'last_completed_compile_min_disk_bytes':last_sample,'recorded_stop':'disk_floor','scope':'No stop-trigger byte value recorded; no endpoint or postflight'},indent=2))
