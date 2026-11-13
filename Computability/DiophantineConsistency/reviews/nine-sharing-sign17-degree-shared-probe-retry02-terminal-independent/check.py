#!/usr/bin/env python3
"""Audit the partial coefficient run, without running Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign17-degree-shared-probe-retry02-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign17-degree-shared-probe-retry02-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==69677 and o['outer_exit_code']==0
assert sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='71983bfcc9040aea90fc60b5c90e7a2a4b48feb59e906fb4052c68377c44b208'
names=['Sign17SyntaxDegree','Sign17SharedDegree00'];assert [r['module'] for r in s['rows']]==names
entries=json.loads((packet/'source-manifest.json').read_text())['rows'];pins={};guards=0
for i,(r,e,n) in enumerate(zip(s['rows'],entries,names)):
 assert e['module']=='DiophantineConsistency.'+n;assert r['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];short=mod.split('.')[-1];assert r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
  if short in pins:assert dep['sha256']==pins[short]
  else:assert short=='Sign17CurrentExpressionDef' and dep['sha256']=='d9342cba53ada4585f27a62d80699d1769f9282bba343281313da886079aa652'
 log=(a/(n+'-compile.txt')).read_text();obj=out/'lib/DiophantineConsistency'/(n+'.olean')
 assert not any(t in log for t in ('sorryAx','error:','warning:')) and sha(obj)==r['object_sha256'];pins[n]=r['object_sha256']
 assert r['object_sha256']==['92eec74fdf59018c09c412203a4c35ff412ed8d327e6c758c24deef87b872a19','b7259469f06aa29666e3312140bac75f2f047b315f63227564b1d9d6a665e911'][i]
 assert ('polynomial_degree_le' if i==0 else 'shared00_degree') in log
 if i==1:assert 'shared04_degree' in log and log.count('[propext, Quot.sound]')==2
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-expression-eval-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':69677,'outer_exit':0,'successful_children':2,'guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'generic syntax degree and five shared-node bounds; no full degree bound'},indent=2,sort_keys=True))
