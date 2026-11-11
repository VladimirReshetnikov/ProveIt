from pathlib import Path
import hashlib,json,subprocess,sys,re
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-fwd09-split-retry01-check';a=p/'attempt01';live=Path('/tmp/current14-k215-fwd09-split-retry01-20261110')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['status']=='PASS' and o['outer_session']==12713 and o['outer_exit_code']==0 and len(o['captured_logs'])==46
assert sha(a/'state.json')==o['state_sha256']=='607b1d847954d5dd613e870e11bd537cf6122a0be80a8c389660f84ee001acbe'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==23 and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='276e8264c6345e9e10daa5c0c2ecb05a8507c1cb6f5ed8b74dcf34a7648094cc' and s['plan_sha256']==sha(p/'plan.json') and s['monitor_sha256']==sha(p/'monitor.py')
plan=json.loads((p/'plan.json').read_text());entries=plan['entries'];assert len(entries)==23
base={x['module']:x for x in json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text())['records']};prior={};guards=0
for i,(e,r) in enumerate(zip(entries,s['rows'])):
 n=e['module'];name=n.replace('.','/');assert n==r['module'] and e['source_sha256']==r['source_sha256'];assert sha(root.parents[1]/e['source'])==sha(live/'src'/f'{name}.lean')==e['source_sha256'];assert set(r['dependencies'])==set(e['imports'])|{'Init'}
 for k in ('deps','compile'):
  v=r[k];q=Path(v['log']);assert sha(q)==sha(a/'logs'/q.name)==v['log_sha256']==o['captured_logs'][q.name];assert v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert v['peak_session_rss_bytes']<v['rss_limit_bytes'] and v['min_disk_free_bytes']>v['disk_floor_bytes'] and v['min_host_available_bytes']>=v['host_floor_bytes'];assert v['exit']==0
 for dep,v in r['dependencies'].items():
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  if dep in prior:assert v==prior[dep]
  elif dep=='Init':assert v['sha256']==plan['external_direct']['Init']['sha256']
  else:assert dep in base and v['sha256']==base[dep]['object_sha256'] and v['realpath'].startswith('/tmp/current14-standard-fresh-build-20261104/lib/')
 for guard in (r['direct_guard'],r.get('output_guard',{})):
  for path,v in guard.items():
   guards+=1;q=Path(path)
   if v is None:assert not q.exists() and not q.is_symlink()
   else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 obj=live/'lib'/f'{name}.olean'
 assert sha(obj)==r['object_sha256'];prior[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':r['object_sha256']}
for pos,side in [(20,'Left'),(21,'Right')]:
 r=s['rows'][pos];text=(a/'logs'/Path(r['compile']['log']).name).read_text();assert text.strip()==f"'SetTheory.BusyBeaver.ZFC.KSource215.fwd9{side}_ok' depends on axioms: [propext]"
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
log=(a/'logs'/Path(s['rows'][-1]['compile']['log']).name).read_text();assert log.strip()=="'SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok9' depends on axioms: [propext]"
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-fwd09-split-retry01-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_INDEPENDENT_TERMINAL_AUDIT','outer_session':12713,'outer_exit':0,'successful_stages':23,'child_checks':'both pass with [propext]','join_axioms':['propext'],'guard_observations':guards,'scope':'Proof-refactored fwd_ok9 checked; full coherent rebuild remains open'},indent=2))
