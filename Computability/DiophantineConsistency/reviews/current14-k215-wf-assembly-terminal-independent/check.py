from pathlib import Path
import hashlib,json,subprocess,sys,re
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-wf-assembly-check';a=p/'attempt01';live=Path('/tmp/current14-k215-wf-assembly-20261110')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
outer=json.loads((a/'outer-result.json').read_text());assert outer['status']=='PASS' and outer['outer_exit_code']==0 and outer['outer_session']==5878
assert sha(a/'state.json')==outer['state_sha256']=='2a500cd29c32dd38e22541120cb633d75d4c32e81695114e94f3ce6638e712fd'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='a27da2a7c0d0fa892515ad4eea2d37a6822d429102122a9b06daf12fad08899d';assert s['plan_sha256']==sha(p/'plan.json');assert s['monitor_sha256']==sha(p/'monitor.py')
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-assembly-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
plan=json.loads((p/'plan.json').read_text());assert len(s['rows'])==len(plan['entries'])==18 and len(outer['captured_logs'])==36
prior={};reports={}
for e,row in zip(plan['entries'],s['rows']):
 n=e['module'];assert n==row['module'] and row['source_sha256']==e['source_sha256'];name=n.replace('.','/')
 assert sha(root.parents[1]/e['source'])==sha(live/'src'/f'{name}.lean')==e['source_sha256']
 obj=live/'lib'/f'{name}.olean';assert sha(obj)==row['object_sha256'];prior[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':row['object_sha256']}
 for k in ('deps','compile'):
  item=row[k];assert item['exit']==0 and item['stop_reason'] is None and not item['monitor_errors'] and not item['observed_descendant_pids']
  log=Path(item['log']);frozen=a/'logs'/log.name;assert sha(log)==sha(frozen)==item['log_sha256']==outer['captured_logs'][log.name]
  assert item['peak_session_rss_bytes']<item['rss_limit_bytes'] and item['min_disk_free_bytes']>item['disk_floor_bytes'] and item['min_host_available_bytes']>=item['host_floor_bytes']
 assert set(row['dependencies'])==set(e['imports'])|{'Init'}
 for dep,x in row['dependencies'].items():
  q=Path(x['path']);assert q.is_file() and str(q.resolve())==x['realpath'] and sha(q)==x['sha256']
  if dep in prior:assert x==prior[dep]
  elif dep=='Init':assert x['sha256']=='d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'
  elif dep=='BusyBeaver.ZFC.RMEquiv':assert x['sha256']=='51fd5571c94774f848e0d41c7c4c425bb15fa91bb690781482c585276821a3d9'
  elif dep=='BusyBeaver.ZFC.DagPerm':assert x['sha256']=='501b7380b3089a2026507fe41d7958afd163044bb0860e59d819dc107eda2b63'
  else:raise AssertionError(dep)
 for guard in (row['direct_guard'],row['output_guard']):
  for path,v in guard.items():
   q=Path(path)
   if v is None: assert not q.exists() and not q.is_symlink()
   else: assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 text=(a/'logs'/Path(row['compile']['log']).name).read_text()
 assert not re.search(r'(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$',text)
 found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
 prefix='SetTheory.BusyBeaver.ZFC.KSource215WfChunks.'
 if e['origin']=='tables':assert found==[]
 elif e['origin']=='chunk':assert found==[(prefix+'wfChunk'+n[-2:],'propext')]
 else:assert found==[(prefix+'wfNodes','propext, Classical.choice, Quot.sound'),(prefix+'wfCheck222','propext, Classical.choice, Quot.sound')]
 reports[n]=found
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
print(json.dumps({'status':'PASS_INDEPENDENT_TERMINAL_AUDIT','outer_session':5878,'outer_exit':0,'stages':18,'node_chunks':16,'indices':'0..486','root_conditions':4,'base_links':1000,'chunk_axioms':['propext'],'assembly_axioms':['propext','Classical.choice','Quot.sound'],'scope':'Copied-table wfCheck; original module compatibility and full coherent rebuild remain open'},indent=2))
