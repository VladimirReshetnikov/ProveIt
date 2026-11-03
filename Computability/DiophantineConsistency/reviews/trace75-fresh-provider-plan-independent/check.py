from pathlib import Path
from hashlib import sha256
import json,os
base=Path('research/trace75-fresh-provider-plan');p=base/'observations/plan-attempt01/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def bundle(stem,suffixes):return {s:rec(str(stem)+s) for s in suffixes}
assert sha(p)=='053d235687f3024ebb10df6d660d0651797b56096e885f9d88fcb2692138217d';j=json.loads(p.read_text());assert j['status']=='PASS' and sha(base/'plan.py')==j['runner_sha256']
for p,h in j['inputs'].items():assert sha(p)==h
scan=json.loads(Path('research/trace75-bfs-provider-preflight/observations/scan-attempt01/result.json').read_text());prior=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text());outer=json.loads(Path('research/trace75-bfs-provider-preflight/observations/outer-attempt01/terminal.json').read_text());assert scan['status']=='PASS' and prior['status']=='PASS' and outer['exit']==0
names=set(scan['roots']['Trace75FixedCongruence']['project']);bfs=set(scan['roots']['DirectBFSBandCarry']['project']);headers=scan['headers'];assert len(names)==208 and len(bfs)==46 and len(names&bfs)==6
seeds={'DiophantineConsistency.ModelRatioBounds','DiophantineConsistency.ArithmeticNegativeNorms'};assert set(j['seeds'])==seeds and seeds<=names
cone=set(seeds)
while True:
 new=cone|{n for n in names if cone.intersection(headers[n])}
 if new==cone:break
 cone=new
assert cone==set(j['affected']) and len(cone)==18
stages={n for n in cone if n.startswith('Trace75')};order=j['stage_order'];assert len(stages)==len(order)==14 and set(order)==stages
for n in stages:
 for d in headers[n]:
  if d in stages:assert order.index(d)<order.index(n),(d,n)
assert cone-stages-seeds=={'DiophantineConsistency.ModelArithmetic','DiophantineConsistency.ModelExponentialCongruence'}
classes=j['classification'];assert {k:len(v) for k,v in classes.items()}=={'identical':152,'different':10,'absent':46};assert set().union(*(set(v) for v in classes.values()))==names and sum(map(len,classes.values()))==len(names)
root=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib')
for kind,entries in classes.items():
 for n,row in entries.items():
  sel=scan['selected_project'][n];assert row['trace']==sel
  suffixes=sel.keys();selected_path=Path(sel['.olean']['path']);assert bundle(str(selected_path)[:-6],suffixes)==sel
  fresh=bundle(root/Path(*n.split('.')),suffixes);assert fresh==row['fresh']
  if fresh['.olean'] is None:expected='absent'
  elif fresh['.olean']['sha256']!=sel['.olean']['sha256']:expected='different'
  else:
   expected='identical'
   for s in suffixes:
    a=sel[s];b=fresh[s];assert (None if a is None else a['sha256'])==(None if b is None else b['sha256']),(n,s)
  assert kind==expected,n
assert bfs&names<=classes['identical'].keys()
for n,v in j['producers'].items():
 assert n in stages
 r=json.loads(Path(v['receipt']).read_text());src=Path(v['source']);att=Path(v['receipt']).parent
 assert sha(v['receipt'])==v['receipt_sha256'] and r['exit']==0 and r['reason'] is None and r['object_sha256']==v['object_sha256']==scan['selected_project'][n]['.olean']['sha256']
 assert sha(src)==v['source_sha256']==r['inputs'][str(src)]==sha(att/'source.txt')
 for s in ['stdout','stderr']:assert sha(att/s)==r[s+'_sha256']
 assert v['stage_imports']==[d for d in headers[n] if d in stages]
assert set(j['producers'])==stages
print('PASS: 208 project classification 152 identical/10 differing/46 absent; 18-node reverse cone (2 seeds, 2 matching objects, 14 stages), stage topological order and all source/producer/log snapshots verified.')
print('BFS subtree 46 nodes: six overlap trace75 and all six classify identical; the other forty are outside the 208 trace75 names, not tested by this classification.')
print('Plan only: no replay, fresh union, compiler compatibility, transitive package/dynamic or historical trace75 provenance established.')
