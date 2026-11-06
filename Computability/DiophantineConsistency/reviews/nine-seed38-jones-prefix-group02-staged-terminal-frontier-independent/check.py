#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group02-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-group02-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='51f86a819ff5fa132782984c56293d3111edf3923be2b2e7a2cb9b3a3079232e'
assert h(a/'outer-terminal-author-record.json')=='b27d13061e0f48a533030e454fd1f70601f39a28a1029dc1ad788e951aa5bc57'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['outer_session_id'],o['outer_exit_code'])==(60427,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4
names=['Norm38MacroPrefixCarry','Norm38MacroPrefixE','Norm38MacroPrefixEll','Norm38MacroPrefixLambda'];objects=['8800799bae0f3693aed496121077ca33d4b2ce5686dc7621e158a0a8d5bedc0e','b1742d0c3c6372d05c31627da4e6f4bc32ad1757a7d20c1e31774109ec3cbe64','bdf292db45b95d08a08d93a886567f773c0462c16bed0a6a8806a7e3b7539712','7f2d141c3f7c256e86f61f7ddef52f5a6025ce872a5ede3d3c1f5f8fd4caba0d'];reports=[['d4_B','d5_B','d6_B'],['prefix_e'],['prefix_ell'],['prefix_lambda']]
for i,(r,n,obj,rs) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in rs:assert re.search(r"'DiophantineConsistency\.Norm38MacroPrefixGroup02\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 depname='DiophantineConsistency.'+('Norm38MacroPrefixGroup01' if i==0 else 'Norm38MacroPrefixCarry');dep=r['dependencies'][depname];expected='a312303ac1f6f1ce780ec12a4f74a8633a22ca6e1779feb675ef6edc8674186a' if i==0 else objects[0];assert dep['sha256']==expected and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':expected}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1170
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':60427,'stages':4,'reports':6,'direct_guard_slots':400,'overlay_links':1170,'scope':'short-prefix symbolic values; no Lean replay'},sort_keys=True,indent=2))
