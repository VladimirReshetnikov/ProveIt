from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); D=R/'Computability/DiophantineConsistency'; p=D/'research/adaptive-expression2011-cache-plan.json'
x=json.loads(p.read_text()); n=0
def check(r):
 global n
 b=Path(r['path']).read_bytes(); assert hashlib.sha256(b).hexdigest()==r['sha256'],r['path']; assert 'bytes' not in r or len(b)==r['bytes']; n+=1
for z in x['pins']:check(z)
mods={m['module']:m for m in x['modules']}; assert len(mods)==52
assert len(x['topological_order'])==52 and set(x['topological_order'])==set(mods)
fresh=set();seen=set()
for name in x['topological_order']:
 m=mods[name];check(m['source']);internal=[d for d in m['imports'] if d in mods];assert all(d in seen for d in internal)
 change=m['source']['sha256']!=m['historical_provider']['source']['sha256']; affected=change or any(d in fresh for d in internal)
 assert affected==(m['mode']=='FRESH_CURRENT_SOURCE_REQUIRED')
 if affected: fresh.add(name);assert not m['selected_objects']
 else:
  assert len(m['selected_objects'])==1
  for z in m['selected_objects']:check(z)
 seen.add(name)
assert fresh==set(x['fresh_prerequisites']) and len(fresh)==24
assert set(x['reused_modules'])==set(mods)-fresh and len(x['reused_modules'])==28
external={e['module'] for e in x['external']};assert len(external)==35
reachable=set()
def visit(name):
 if name in reachable:return
 reachable.add(name)
 for d in mods[name]['imports']:
  if d in mods:visit(d)
  else:assert d in external,d
for name in x['direct_imports']:visit(name)
assert reachable==set(mods)
for e in x['external']:
 check(e['source'])
 for a in e['artifacts']:check(a)
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps({'status':'PASS','plan_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'observations':n,'scope':'52 exact reachable modules; 24 current-source affected and 28 cached, 35 explicit package boundaries; all frozen pins rehashed','free_bytes':shutil.disk_usage('/tmp').free},indent=2))
