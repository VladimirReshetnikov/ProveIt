from pathlib import Path
import hashlib,json,subprocess,sys,re
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-wf-last-chunk-check';a=p/'attempt01';live=Path('/tmp/current14-k215-wf-last-chunk-20261110')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
outer=json.loads((a/'outer-result.json').read_text());assert outer['status']=='PASS' and outer['outer_exit_code']==0 and outer['outer_session']==29721
assert sha(a/'state.json')==outer['state_sha256']=='8b7e36c5bc9567b5b58d8fea90e773930c6f89ad6f9746cbd7f43d81266ad01a'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='b3961cec6eff8e7adb98ae0bba8a9bdd8377ea365600e690957b68053732157a';assert s['plan_sha256']==sha(p/'plan.json');assert s['monitor_sha256']==sha(p/'monitor.py')
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-last-chunk-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
plan=json.loads((p/'plan.json').read_text());assert len(s['rows'])==2
for e,row in zip(plan['entries'],s['rows']):
 n=e['module'];assert n==row['module'] and row['source_sha256']==e['source_sha256'];name=n.replace('.','/')
 assert sha(root.parents[1]/e['source'])==sha(live/'src'/f'{name}.lean')==e['source_sha256']
 assert sha(live/'lib'/f'{name}.olean')==row['object_sha256']
 for k in ('deps','compile'):
  item=row[k];assert item['exit']==0 and item['stop_reason'] is None and not item['monitor_errors'] and not item['observed_descendant_pids']
  log=Path(item['log']);frozen=a/'logs'/log.name;assert sha(log)==sha(frozen)==item['log_sha256']==outer['captured_logs'][log.name]
  assert item['peak_session_rss_bytes']<item['rss_limit_bytes'] and item['min_disk_free_bytes']>item['disk_floor_bytes'] and item['min_host_available_bytes']>=item['host_floor_bytes']
 assert set(row['dependencies'])==set(e['imports'])|{'Init'}
 for x in row['dependencies'].values():
  q=Path(x['path']);assert q.is_file() and str(q.resolve())==x['realpath'] and sha(q)==x['sha256']
 for guard in (row['direct_guard'],row['output_guard']):
  for name,v in guard.items():
   q=Path(name)
   if v is None: assert not q.exists() and not q.is_symlink()
   else: assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
log=(a/'logs'/'001-BusyBeaver_ZFC_KSource215WfChunk15-compile.txt').read_text();assert log.strip()=="'SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfChunk15' depends on axioms: [propext]"
print(json.dumps({'status':'PASS_INDEPENDENT_TERMINAL_AUDIT','outer_session':29721,'outer_exit':0,'stages':2,'base_links':1000,'axioms':['propext'],'scope':'Only nodeOkb indices 480–486; remaining nodes, root facts and full assembly open'},indent=2))
