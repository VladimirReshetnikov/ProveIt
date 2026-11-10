#!/usr/bin/env python3
"""Review count client and its passed shape provider with failed grandparent."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign20-count-proof-check';draft=research/'nine-sharing-sign20-count-proof-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
manifest=p/'source-manifest.json';assert sha(manifest)=='7fc3a533b891f020e24235ce1aa1148d62367d8b244dfc146de8018d60a197cf';e,=json.loads(manifest.read_text())['rows'];assert e['module']=='DiophantineConsistency.Sign20CountProof' and e['imports']==['DiophantineConsistency.Sign20CountShapes']
src=p/'src/DiophantineConsistency/Sign20CountProof.lean';s=src.read_text();assert sha(src)==sha(draft/'Sign20CountProof.lean')==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']
for name,own in (('n0',3),('dc2',1)):
 section=s.split(f'theorem {name}_count',1)[1].split('\n\n',1)[0];assert f'(SharingSeed20Degree20.remainingResiduals p).count ({name} p) = 1' in section and f'hself : row p {own} = {name} p := by rfl' in section
 for i in range(10):
  if i!=own:assert f'row p {i} ≠ {name} p := ({name}_ne_{i} p).symm' in section
 assert 'List.count_cons, beq_iff_eq' in section
assert s.count('set_option maxHeartbeats 4000000 in')==2 and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
runner=p/'run.py';assert sha(runner)=='2e0cd195ae7b491141a7cefa906dbbfce419a7075e439a27193bd6084fca74dd';r=runner.read_text();assert "base['status']=='PASS' and len(base['rows'])==1" in r and "['outer_exit_code']==0" in r and "if local=='Sign20CountShapes':expected_hash=base['rows'][0]['object_sha256']" in r
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-count-shapes-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'two proposed finite counts from 18 shape inequalities; passed provider has failed-grandparent ancestry, no Lean count/lower theorem'},indent=2,sort_keys=True))
