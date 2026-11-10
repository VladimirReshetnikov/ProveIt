#!/usr/bin/env python3
"""Audit the partial coefficient run, without running Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign20-full-coeff-retry03-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign20-full-coeff-retry03-20261109');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==43491 and o['outer_exit_code']==1
assert sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign20SeedCoefficient')" and s['runner_sha256']==sha(packet/'run.py')=='a592544ed5133152b0fb5513ec802a3c5585a74f1fedcbc18de6e08c935165a7'
names=['Sign20LeadingRows','Sign20DiagonalDegree','Sign20AxisResidualDegree','Sign20SquareCoeffs','Sign20AxisCoeffLemmas','Sign20SeedCoefficient'];assert [r['module'] for r in s['rows']]==names
entries=json.loads((packet/'source-manifest.json').read_text())['rows'];pins={};guards=0
for i,(r,e,n) in enumerate(zip(s['rows'],entries,names)):
 assert e['module']=='DiophantineConsistency.'+n;assert r['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==(1 if i==5 and phase=='compile' else 0) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];short=mod.split('.')[-1];assert r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
  if short in pins:assert dep['sha256']==pins[short]
  else:assert short=='Sign20CurrentExpressionDef' and dep['sha256']=='325ed61a2f8d6f4af8516240f782f83d5ca83579c8184a7fad5dc066d02f96a3'
 log=(a/(n+'-compile.txt')).read_text();obj=out/'lib/DiophantineConsistency'/(n+'.olean')
 if i<5:assert 'sorryAx' not in log and 'error:' not in log and sha(obj)==r['object_sha256'];pins[n]=r['object_sha256']
 else:assert log.count('error: unsolved goals')==2 and log.count('sorryAx')==3 and not obj.exists() and 'object_sha256' not in r
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','outer_session':43491,'outer_exit':1,'successful_children':5,'failed_child':'Sign20SeedCoefficient','guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'first five stages pass; seed coefficient fails with sorryAx; lower stage and final postflight absent'},indent=2,sort_keys=True))
