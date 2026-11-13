#!/usr/bin/env python3
"""Inspect current-beta retry receipt and direct provider without Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-gap-from-seed-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-gap-from-seed-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==24160 and o['outer_exit_code']==0
assert sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='808789500a9be7df14d344616be18bcf73531b72a2d132b127ee0a9dcdb7508f'
r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17GapFromSeed';assert r['module']==n and r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(n+'.olean'))=='a4a985bb7857e1aac11cc97d1d1ef675a6258536cf851d8dff768b938d68006a'
for phase in ('deps','compile'):
 x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
pins={'Sign17ConcreteGap':'d378fe73bceeb6daf78a05287622677f4ac02dc743a7f5ce075296531fdd6f18','SharingSign17Squares':'51f81afaba554534380a855369a46664e7897e9c89f1335c02e3704ccfd90be2'}
for mod in e['imports']:
 d=r['dependencies'][mod];assert d['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert not any(x in log for x in ('warning:','error:','sorryAx'))
for th in ('exists_gap',):assert "'DiophantineConsistency.Sign17GapFromSeed."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-concrete-root-retry-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(p/'staged-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['overlay_overlap']==1057
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':24160,'outer_exit':0,'guard_entries':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'actual staged seed zero yields model-natural gap under beta>0 and port equality; no full zero bridge'},indent=2,sort_keys=True))
