from pathlib import Path
import hashlib,json,subprocess,sys,re
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-wf-chunk-probe-check';a=p/'attempt01';live=Path('/tmp/current14-k215-wf-chunk-probe-20261110')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
outer=json.loads((a/'outer-result.json').read_text());assert outer['status']=='PASS' and outer['outer_exit_code']==0 and outer['outer_session']==53221
assert sha(a/'state.json')==outer['state_sha256']=='30a23fc26fe665b1b71f3d919ab3d15d55d6a5edaae7be9be346c6b2e76582f7'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='8671cbb8aedbc97bce7ec6cf7f05d9b2e17177c28e2cda3c167ba3f21543164c';assert s['plan_sha256']==sha(p/'plan.json');assert s['monitor_sha256']==sha(p/'monitor.py')
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-chunk-probe-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
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
log=(a/'logs'/'001-BusyBeaver_ZFC_KSource215WfChunk00-compile.txt').read_text();assert log.strip()=="'SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfChunk00' depends on axioms: [propext]"
print(json.dumps({'status':'PASS_INDEPENDENT_TERMINAL_AUDIT','outer_session':53221,'outer_exit':0,'stages':2,'base_links':1000,'axioms':['propext'],'scope':'Only nodeOkb indices 0–31; remaining nodes, root facts and full assembly open'},indent=2))
