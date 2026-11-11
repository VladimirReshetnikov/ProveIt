from pathlib import Path
import hashlib,json,subprocess,sys,re
root=Path(__file__).resolve().parents[2];p=root/'research/current14-auxiliary-order-generic-cast-check';a=p/'attempt01';live=Path('/tmp/current14-auxiliary-order-generic-cast-20261110');parent=Path('/tmp/current14-coherent490-refactor-retry03-20261110');cache={}
def sha(p):
 p=Path(p);st=p.stat();key=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
 if key not in cache:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
  st=p.stat();assert (st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)==key;cache[key]=h.hexdigest()
 return cache[key]
o=json.loads((a/'outer-result.json').read_text());assert o['status']=='PASS' and o['outer_session']==61084 and o['outer_exit_code']==0 and len(o['captured_logs'])==4
assert sha(a/'state.json')==o['state_sha256']=='21a43c864882025b84e49308fef7b262c07fb085718490a83df87ae1f1ca54d7';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='9d9306094d30286753cf401abb0a29ef2670fdc56e8945c7d24c935c1aee4746' and s['plan_sha256']==sha(p/'plan.json') and s['monitor_sha256']==sha(p/'monitor.py')
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-coherent-extension-refactor-retry03-failure-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-auxiliary-order-generic-cast-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
ps=json.loads((root/'research/current14-coherent-extension-refactor-retry03-runner/attempt01/state.json').read_text());assert ps['status']=='FAILED' and len(ps['rows'])==418 and ps['rows'][-1]['compile']['exit']==1
assert len(s['provider_links'])==417
for r in ps['rows'][:417]:
 name=r['module'].replace('.','/');q=live/'lib'/f'{name}.olean';v=s['provider_links'][str(q)];assert q.is_symlink() and str(q.resolve())==v['realpath']==str((parent/'lib'/f'{name}.olean').resolve()) and sha(q)==v['sha256']==r['object_sha256']
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
entries=[('DiophantineConsistency.CurrentAuxiliaryOrder2011',root/'research/current14-auxiliary-order-generic-cast-draft/CurrentAuxiliaryOrder2011.lean',['DiophantineConsistency.PrimePowerOrder','DiophantineConsistency.CurrentControllerData2011']),('DiophantineConsistency.AuxiliaryOrderAudit',p/'AuxiliaryOrderAudit.lean',['DiophantineConsistency.CurrentAuxiliaryOrder2011'])];prior={};guards=0
for (n,src,imports),r in zip(entries,s['rows']):
 name=n.replace('.','/');assert r['module']==n and sha(src)==sha(live/'src'/f'{name}.lean')==r['source_sha256'];assert set(r['dependencies'])==set(imports)|{'Init'}
 for k in ('deps','compile'):
  v=r[k];q=Path(v['log']);assert sha(q)==sha(a/'logs'/q.name)==v['log_sha256']==o['captured_logs'][q.name];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert v['peak_session_rss_bytes']<v['rss_limit_bytes'] and v['min_disk_free_bytes']>v['disk_floor_bytes'] and v['min_host_available_bytes']>=v['host_floor_bytes']
 for dep,v in r['dependencies'].items():
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  if dep in prior:assert v==prior[dep]
  elif dep=='Init':assert v['sha256']=='d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'
  else:assert str(q) in s['provider_links'] and v['sha256']==s['provider_links'][str(q)]['sha256'] and v['realpath']==s['provider_links'][str(q)]['realpath']
 for guard in (r['direct_guard'],r['output_guard']):
  for path,v in guard.items():
   guards+=1;q=Path(path)
   if v is None:assert not q.exists() and not q.is_symlink()
   else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 obj=live/'lib'/f'{name}.olean';assert sha(obj)==r['object_sha256'];prior[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':r['object_sha256']}
 assert not re.search(r'(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$',(a/'logs'/Path(r['compile']['log']).name).read_text())
log=(a/'logs'/Path(s['rows'][-1]['compile']['log']).name).read_text();found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);reports={n:{x.strip() for x in b.split(',')} for n,b in found};prefix='DiophantineConsistency.CurrentAuxiliaryOrder2011.';assert reports=={prefix+'generator_order_succ':{'propext','Classical.choice','Quot.sound'},prefix+'generator_order':{'propext','Classical.choice','Quot.sound'}}
print(json.dumps({'status':'PASS_INDEPENDENT_TERMINAL_AUDIT','outer_session':61084,'outer_exit':0,'stages':2,'provider_parent':'FAILED','individually_successful_provider_links':417,'base_links':1000,'guard_observations':guards,'target_peak_sampled_rss_bytes':s['rows'][0]['compile']['peak_session_rss_bytes'],'scope':'Point-in-time generic-cast proof refactor; no coherent rebuild established'},indent=2))
