from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-wang942core-staged-check';a=p/'attempt01';live=Path('/tmp/current14-wang942core-staged-20261110');parent=Path('/tmp/current14-coherent490-refactor-retry04-20261110');cache={}
def sha(p):
 p=Path(p);st=p.stat();key=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
 if key not in cache:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
  st=p.stat();assert (st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)==key;cache[key]=h.hexdigest()
 return cache[key]
o=json.loads((a/'outer-result.json').read_text());assert o['status']=='FAILED' and o['outer_session']==60488 and o['outer_exit_code']==1 and len(o['captured_logs'])==4
assert sha(a/'state.json')==o['state_sha256']=='25bd654c26319307f423c03c90b6c8fcbbd9d42c23c09a01c207db4b3622fcf7';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==2 and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='a9af3857b575f4be83ceaa5100fdb434406898142cce891648e797380cfd33a8' and s['plan_sha256']==sha(p/'plan.json') and s['monitor_sha256']==sha(p/'monitor.py')
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-coherent-extension-refactor-retry04-failure-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-wang942core-staged-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
ps=json.loads((root/'research/current14-coherent-extension-refactor-retry04-runner/attempt01/state.json').read_text());assert ps['status']=='FAILED' and len(ps['rows'])==399 and ps['rows'][-1]['compile']['exit']==-6
assert len(s['provider_links'])==398
for r in ps['rows'][:398]:
 name=r['module'].replace('.','/');q=live/'lib'/f'{name}.olean';v=s['provider_links'][str(q)];assert q.is_symlink() and str(q.resolve())==v['realpath']==str((parent/'lib'/f'{name}.olean').resolve()) and sha(q)==v['sha256']==r['object_sha256']
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
entries=[('DiophantineConsistency.WangTiles942CoreA',['DiophantineConsistency.WangTiles942TableData','DiophantineConsistency.WangTiles942Data','Mathlib.Tactic']),('DiophantineConsistency.WangTiles942CoreB',['DiophantineConsistency.WangTiles942CoreA'])];prior={};guards=0;plan=json.loads((p/'plan.json').read_text());base={x['module']:x for x in json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text())['records']}
for i,((n,imports),r) in enumerate(zip(entries,s['rows'])):
 name=n.replace('.','/');src=root/'research/current14-wang942core-staged-draft'/f'{n.split(".")[-1]}.lean';assert r['module']==n and sha(src)==sha(live/'src'/f'{name}.lean')==r['source_sha256'];assert set(r['dependencies'])==set(imports)|{'Init'}
 for k in ('deps','compile'):
  v=r[k];q=Path(v['log']);assert sha(q)==sha(a/'logs'/q.name)==v['log_sha256']==o['captured_logs'][q.name];assert v['exit']==(1 if i==1 and k=='compile' else 0) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert v['peak_session_rss_bytes']<v['rss_limit_bytes'] and v['min_disk_free_bytes']>v['disk_floor_bytes'] and v['min_host_available_bytes']>=v['host_floor_bytes']
 for dep,v in r['dependencies'].items():
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  if dep in prior:assert v==prior[dep]
  elif dep=='Init':assert v['sha256']==plan['external_direct']['Init']['sha256']
  elif str(q) in s['provider_links']:assert v['sha256']==s['provider_links'][str(q)]['sha256'] and v['realpath']==s['provider_links'][str(q)]['realpath']
  elif dep in base:assert v['sha256']==base[dep]['object_sha256'] and v['realpath'].startswith('/tmp/current14-standard-fresh-build-20261104/lib/')
  else:assert dep in plan['external_direct'] and v['sha256']==plan['external_direct'][dep]['sha256'] and v['realpath']==plan['external_direct'][dep]['realpath']
 for guard in (r['direct_guard'],r.get('output_guard',{})):
  for path,v in guard.items():
   guards+=1;q=Path(path)
   if v is None:assert not q.exists() and not q.is_symlink()
   else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 obj=live/'lib'/f'{name}.olean'
 if i==0:assert sha(obj)==r['object_sha256'];prior[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':r['object_sha256']}
 else:assert not obj.exists() and 'object_sha256' not in r
log=(a/'logs'/Path(s['rows'][-1]['compile']['log']).name).read_text();assert ':24:2: error: Tactic `decide` failed' in log and '(kernel) excessive memory consumption detected' in log
assert s['failure']=="Refusal('compile failed DiophantineConsistency.WangTiles942CoreB')"
print(json.dumps({'status':'PASS_INDEPENDENT_FAILURE_AUDIT','outer_session':60488,'outer_exit':1,'successful_stages':1,'provider_parent':'FAILED','individual_provider_links':398,'base_links':1000,'failed_stage':'WangTiles942CoreB','failed_child_exit':1,'monitor_stop':None,'peak_sampled_rss_bytes':s['rows'][-1]['compile']['peak_session_rss_bytes'],'guard_observations':guards,'scope':'CoreA only; CoreB kernel memory/no object; no final module or coherent build'},indent=2))
