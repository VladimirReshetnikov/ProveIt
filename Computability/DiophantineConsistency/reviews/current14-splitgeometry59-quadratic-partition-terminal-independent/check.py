from pathlib import Path
import hashlib,json,subprocess,sys,re
root=Path(__file__).resolve().parents[2];p=root/'research/current14-splitgeometry59-quadratic-partition-check';a=p/'attempt01';live=Path('/tmp/current14-splitgeometry59-quadratic-partition-20261110')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['status']=='PASS' and o['outer_session']==9079 and o['outer_exit_code']==0 and len(o['captured_logs'])==252
assert sha(a/'state.json')==o['state_sha256']=='64eec2456c917a949007c5887ad38be381d4ef36d341ead66fed876c03f2def0';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==126 and sha(live/'state.json')==sha(a/'state.json')
assert s['runner_sha256']==sha(p/'run.py')=='2ae635ce931d6c867e4f5212ac5527804047ab111329df4740ba10add174857b' and s['plan_sha256']==sha(p/'plan.json') and s['monitor_sha256']==sha(p/'monitor.py')
plan=json.loads((p/'plan.json').read_text());entries=plan['entries'][:124];assert len(entries)==124
partition=root/'research/current14-splitgeometry59-quadratic-partition-draft/SplitGeometry59.lean';client=p/'SplitGeometry59Audit.lean'
assert sha(partition)=='191c880fd6543e036c832333073aada2720c5f4b0f014ada4bc2c15e5400700e' and sha(client)=='2e18db0a5bb47d00d42ae3f9099a3e9f8069bf977045d785f80c82c58209b29a'
entries += [dict(plan['entries'][124],source=str(partition.relative_to(root.parents[1])),source_sha256=sha(partition)),{'module':'DiophantineConsistency.SplitGeometry59Audit','source':str(client.relative_to(root.parents[1])),'source_sha256':sha(client),'imports':['DiophantineConsistency.SplitGeometry59'],'origin':'audit','old_parent_status':None}]
base={x['module']:x for x in json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text())['records']};prior={};totalguards=0
for e,r in zip(entries,s['rows']):
 n=e['module'];name=n.replace('.','/');assert n==r['module'] and e['source_sha256']==r['source_sha256'];assert sha(root.parents[1]/e['source'])==sha(live/'src'/f'{name}.lean')==e['source_sha256'];assert set(r['dependencies'])==set(e['imports'])|{'Init'}
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
   totalguards+=1;q=Path(path)
   if v is None:assert not q.exists() and not q.is_symlink()
   else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 obj=live/'lib'/f'{name}.olean';assert sha(obj)==r['object_sha256'];prior[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':r['object_sha256']}
 assert not re.search(r'(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$',(a/'logs'/Path(r['compile']['log']).name).read_text())
assert len(s['base_links'])==1000
for path,v in s['base_links'].items():
 q=Path(path);assert q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert sum(r['old_parent_status']=='FAILED' for r in s['rows'])==4
log=(a/'logs'/Path(s['rows'][-1]['compile']['log']).name).read_text();found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);reports={n:{a.strip() for a in body.split(',')} for n,body in found};prefix='DiophantineConsistency.SplitCertificate59.';assert reports=={prefix+'linear_cross':{'propext','Quot.sound'},prefix+'quadratic_cross':{'propext','Classical.choice','Quot.sound'},prefix+'targetPositions_range':{'propext','Classical.choice','Quot.sound'}}
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-splitgeometry59-quadratic-partition-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_INDEPENDENT_TERMINAL_AUDIT','outer_session':9079,'outer_exit':0,'stages':126,'base_links':1000,'guard_observations':totalguards,'target_compile_seconds':s['rows'][-2]['compile']['elapsed_seconds'],'target_peak_sampled_rss_bytes':s['rows'][-2]['compile']['peak_session_rss_bytes'],'scope':'Proof-refactored SplitGeometry59 and 3 audit reports; coherent endpoint/full rebuild remain open'},indent=2))
