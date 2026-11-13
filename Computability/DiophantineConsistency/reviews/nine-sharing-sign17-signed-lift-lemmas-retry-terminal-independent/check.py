#!/usr/bin/env python3
"""Inspect passed conditional lower and failed-grandparent diagonal child."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-signed-lift-lemmas-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-signed-lift-lemmas-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==44638 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json')
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and s['runner_sha256']==sha(p/'run.py')=='0ae0eee3264495a5fbb6dc09c18a2702d9e6aec7890909de811355dfb406734c'
names=['Sign17OrderedGap','Sign17GapRepresentative'];obj=['157ba8307d5bcf118e642cd3ca592d706bfe36ff5cb818696c4dcaf939f95a09','f33b5757b138c2a88a9fc0799aba1b6d2ea6c60598d300c8571e74a84be55ab9'];pins={'Sign20CurrentExpressionDef':'325ed61a2f8d6f4af8516240f782f83d5ca83579c8184a7fad5dc066d02f96a3',**dict(zip(names,obj))};entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert [r['module'] for r in s['rows']]==names;guards=0
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
 ns='Sign17OrderedGap' if i==0 else 'Sign17GapRepresentative'
 for th in (('root_positive','scale_positive','difference_nonnegative') if i==0 else ('exists_gap',)):assert "'DiophantineConsistency."+ns+'.'+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
for review in ('nine-sharing-sign17-signed-lift-lemmas-failure-independent',):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':44638,'outer_exit':0,'stages':2,'guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'generic ordered-ring gap and model-natural representative under hypotheses; no concrete sign17 bridge or endpoint'},indent=2,sort_keys=True))
