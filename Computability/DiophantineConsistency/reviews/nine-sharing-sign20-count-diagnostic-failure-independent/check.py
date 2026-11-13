#!/usr/bin/env python3
"""Audit the partial coefficient run, without running Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign20-count-diagnostic-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign20-count-diagnostic-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==59172 and o['outer_exit_code']==1
assert sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign20CountDiagnostic')" and s['runner_sha256']==sha(packet/'run.py')=='0854fc80845b9aff925fa977b85029ecfde51ca0a7377e1397c125becb92c531'
names=['Sign20CountDiagnostic'];assert [r['module'] for r in s['rows']]==names
entries=json.loads((packet/'source-manifest.json').read_text())['rows'];pins={};guards=0
for i,(r,e,n) in enumerate(zip(s['rows'],entries,names)):
 assert e['module']=='DiophantineConsistency.'+n;assert r['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==(1 if i==0 and phase=='compile' else 0) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];short=mod.split('.')[-1];assert r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
  if short in pins:assert dep['sha256']==pins[short]
  else:assert short=='Sign20AxisCoeffLemmas' and dep['sha256']=='385be2ce492e69748524790d046cc4cbcb399ac105c70e42d8d4828b5206be54'
 log=(a/(n+'-compile.txt')).read_text();obj=out/'lib/DiophantineConsistency'/(n+'.olean')
 if i<0:assert 'sorryAx' not in log and 'error:' not in log and sha(obj)==r['object_sha256'];pins[n]=r['object_sha256']
 else:assert log.count('error: unsolved goals')==2 and log.count('sorryAx')==2 and not obj.exists() and 'object_sha256' not in r
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert s['base_state_sha256']=='d9dc10f0d38cfb7875ddcad092cb35abf30c77f13972393ba49af1c3b117b789'
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','outer_session':59172,'outer_exit':1,'successful_children':0,'failed_child':'Sign20CountDiagnostic','guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'count diagnostic fails with sorryAx; no object or final postflight'},indent=2,sort_keys=True))
