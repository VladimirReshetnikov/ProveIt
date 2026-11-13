#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group03-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-group03-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='a29549dbd88499b8008252f510c4ffadc8ab5262bdc4b97a820c05271642c59b' and h(a/'outer-terminal-author-record.json')=='7e36fd89812509d860fa00493a293e5a5625d47d3997af0a720609baa74753fa'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['outer_session_id'],o['outer_exit_code'])==(84351,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4
names=['Norm38MacroPrefixCarry03','Norm38MacroPrefixGsmall','Norm38MacroPrefixTheta','Norm38MacroPrefixGlarge'];objects=['59e33ac6b180f893896faa3f5c5e1ce1a8dc54310ace7b3a82cb879c807a3bf3','dd500df7b9ea630528181ee3e1ac62f955822471a9f3385e0a833c13758dbaf2','6c76ea5f4ab7a4390bad1fd78c54fd95353d23af842596a0823d72d8fb088a64','b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06'];reports=[['d8_B','d9_B','d9_b'],['prefix_g'],['prefix_theta'],['prefix_G']]
for i,(r,n,obj,rs) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in rs:assert re.search(r"'DiophantineConsistency\.Norm38MacroPrefixGroup03\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 depname='DiophantineConsistency.'+('Norm38MacroPrefixCarry' if i==0 else 'Norm38MacroPrefixCarry03');dep=r['dependencies'][depname];expected='8800799bae0f3693aed496121077ca33d4b2ce5686dc7621e158a0a8d5bedc0e' if i==0 else objects[0];assert dep['sha256']==expected and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':expected}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1174
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':84351,'stages':4,'reports':6,'direct_guard_slots':400,'overlay_links':1174,'scope':'short-prefix symbolic values; no Lean replay'},sort_keys=True,indent=2))
