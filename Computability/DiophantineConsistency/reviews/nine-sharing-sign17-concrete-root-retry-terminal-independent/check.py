#!/usr/bin/env python3
"""Inspect passed conditional lower and failed-grandparent diagonal child."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-concrete-root-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-concrete-root-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==45324 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json')
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and s['runner_sha256']==sha(p/'run.py')=='8753f3c4cc3d71577d6fc61717fdbd53fd9e1197db7058e58bb74f01360ee40e'
names=['Sign17ConcreteRoot','Sign17ConcreteGap'];obj=['91b8eb97d3a65dec6e304f4eeb5bb130f087b5c36a78c2b0866e223cc58aef1e','d378fe73bceeb6daf78a05287622677f4ac02dc743a7f5ce075296531fdd6f18'];pins={'SharingSeed17Row06':'f61a66d97ea216b92893518b77970870d465218531e9ba652ea22f08f456afb3','Sign17RootLift':'a9e50bc6101443cfadb386692232bab6b19e69d573feefc873285e20aa4727b3',**dict(zip(names,obj))};entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert [r['module'] for r in s['rows']]==names;guards=0
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
 ns='Sign17ConcreteRoot'
 for th in (('shared07_eval','shared24_eval','shared26_eval','shared29_eval','shared33_eval') if i==0 else ('row06_eval','exists_from_row06')):assert "'DiophantineConsistency."+ns+'.'+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
for review in ('nine-sharing-sign17-root-lift-terminal-independent','nine-sharing-sign17-staged-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(p/'staged-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['overlay_overlap']==1057
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':45324,'outer_exit':0,'stages':2,'guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'actual staged Na row gives model-natural gap under beta>0 and port equality; no full bridge or JSON binding'},indent=2,sort_keys=True))
