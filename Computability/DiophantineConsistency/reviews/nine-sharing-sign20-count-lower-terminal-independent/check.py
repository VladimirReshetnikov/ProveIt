#!/usr/bin/env python3
"""Inspect passed conditional lower and failed-grandparent diagonal child."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign20-count-lower-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign20-count-lower-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==94006 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json')
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and s['runner_sha256']==sha(p/'run.py')=='1796953a61e1d7a5f717ccf3021b85982df04b006166e9ef9fa74c102ba1b794'
names=['Sign20SeedCoefficient','Sign20DegreeLower'];obj=['63be389abf265efb65221b6142672ac4db01f16c8033fe738940b9c4b9af8d02','cd2691f4980c164d1816e0459d8ab9ff61cc8bbbf1ff1ad3d476848dc5ff1e0d'];pins={'Sign20CountProof':'28f3f2bdd30585230d8939f46e3059f7d65a61e56519de0a331760c569628ff6','Sign20DiagonalDegree':'6f93b761be7a130a6e0609b24792219c5d63f4b859ac21dd1e22fc7c7bdf75af',**dict(zip(names,obj))};entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert [r['module'] for r in s['rows']]==names;guards=0
for i,(r,e,n,h) in enumerate(zip(s['rows'],entries,names,obj)):
 src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==r['source_sha256']==e['source_sha256']==sha(out/'src/DiophantineConsistency'/(n+'.lean'));assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']==h
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  d=r['dependencies'][mod];assert d['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert not any(x in log for x in ('warning:','error:','sorryAx'))
 for th in (('seed_axis_coeff',) if i==0 else ('diagonal_eval','direct_axis','expression_polynomial_degree_ge')):assert "'DiophantineConsistency.Sign20LeadingRows."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
assert '(hp : p 0 ≠ 0)' in (p/'src/DiophantineConsistency/Sign20DegreeLower.lean').read_text()
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
for review in ('nine-sharing-sign20-count-proof-terminal-independent','nine-sharing-sign20-full-coeff-retry03-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':94006,'outer_exit':0,'stages':2,'guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'axis coefficient 2*(p 0)^4; Fin20 degree ≥20 under p 0 ≠ 0; diagonal is successful child of failed grandparent; no exact degree or external binding'},indent=2,sort_keys=True))
