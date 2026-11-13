#!/usr/bin/env python3
"""Inspect the twelve-stage sign19 run; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign15-staged-syntax-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign15-staged-syntax-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==82930 and o['author_observed_numeric_outer_exit']==0
assert sha(a/'state.json')==sha(out/'state.json')==o['state_sha256']
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s;assert s['runner_sha256']==sha(packet/'run.py')=='d618c33828ad44d26214c3647623f739ff6aad75232b09592b0b0f432704338d'
manifest=json.loads((packet/'source-manifest.json').read_text())['rows'];names=[f'SharingSeed15Shared{i:02}' for i in range(8)]+[f'SharingSeed15Row{i:02}' for i in range(6)]+['SharingSeed15Degree124','SharingSign15Squares'];assert [r['module'] for r in s['rows']]==names
pins={};guards=0;warnings=0
for r,e,n in zip(s['rows'],manifest,names):
 assert e['module']=='DiophantineConsistency.'+n
 assert r['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==o['logs'][log]==x['log_sha256']
 for path,v in r['direct_guard'].items():
  p=Path(path)
  if v is None:assert not os.path.lexists(p)
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];short=mod.split('.')[-1];assert r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
  if short in pins:assert dep['sha256']==pins[short] and dep['realpath']==str((out/'lib/DiophantineConsistency'/(short+'.olean')).resolve())
  elif short=='NineFreshJones':assert dep['sha256']=='9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df'
  elif short=='SharingSign33Squares':assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42'
  else:raise AssertionError(short)
 pins[n]=sha(out/'lib/DiophantineConsistency'/(n+'.olean'));assert pins[n]==r['object_sha256']
 log=(a/(n+'-compile.txt')).read_text();assert 'sorryAx' not in log and 'error:' not in log;warnings+=log.count('warning:')
assert warnings==0
log=(a/'SharingSign15Squares-compile.txt').read_text();assert "'DiophantineConsistency.SharingSign15Squares.seed_zero_iff_residuals' depends on axioms:" in log and all(x in log for x in ('propext','Classical.choice','Quot.sound'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':82930,'outer_exit':0,'stages':16,'guard_entries':guards,'overlay_links':len(s['overlay_links']),'warnings':warnings,'scope':'Lean seed-zero iff staged residuals; external JSON not bound inside Lean, no sign15 model bridge or endpoint'},indent=2,sort_keys=True))
