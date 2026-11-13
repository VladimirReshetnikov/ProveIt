#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent01-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent01-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='ef3978e17c63d717b894c25da20012178cce2ccf398e72bb668ddf67105a8618' and h(a/'outer-terminal-author-record.json')=='95e4569c36e21ba4a8b8c737cd80ba43f972091cfc852af4e4cc258dcd0c7d5d'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(25550,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Norm38MacroDependentU','Norm38MacroDependentY'];objects=['c6b6da9606634431ea1d17f5582628d6c511a4156225466eff4eab5242d5109e','eb28e13077c175963702682ff8501cb25c4036813d5d035c3574a9e605f516a9'];reports=['prefix_U','prefix_Y']
for i,(r,n,obj,t) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log;assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent01\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 dep=r['dependencies']['DiophantineConsistency.'+('Norm38MacroLive18Group01' if i==0 else 'Norm38MacroDependentU')];sha='b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd' if i==0 else objects[0];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1193
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':25550,'stages':2,'reports':2,'direct_guard_slots':200,'overlay_links':1193,'scope':'U/Y short-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
