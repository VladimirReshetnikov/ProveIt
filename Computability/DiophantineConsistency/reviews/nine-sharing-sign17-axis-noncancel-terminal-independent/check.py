#!/usr/bin/env python3
"""Audit failed axis-base two-stage attempt without rerunning Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-noncancel-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-axis-noncancel-20261110');sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==63895 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(p/'run.py')=='0300e605cc04a1c07eaff066f1126223829f809b50d2cc9daddd9e10002abf8f';names=['Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot','Sign17AxisDegreeScale','Sign17AxisBindingBase','Sign17AxisBindingFactors','Sign17AxisBindingRoot','Sign17AxisNaDegree','Sign17AxisOtherDegree','Sign17AxisNoncancel'];assert [r['module'] for r in s['rows']]==names;rows=json.loads((p/'source-manifest.json').read_text())['rows'];pins={'Sign17DegreeCompose':'4af0d401fc347ac92ce4d038699b9b5b0db6dd020c879a5821040aef9dca7d82','Equiv':'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f'};guards=0
for i,(row,e,name) in enumerate(zip(s['rows'],rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');assert row['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
 for phase in ('deps','compile'):
  x=row[phase];log=name+'-'+phase+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(out/log)==x['log_sha256']
  if i==9:assert sha(a/(phase+'.txt'))==x['log_sha256']
 for path,v in row['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=row['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 obj=out/'lib/DiophantineConsistency'/(name+'.olean');log=(out/(name+'-compile.txt')).read_text()
 if i==0:assert 'sorryAx' not in log and 'error:' not in log and row['object_sha256']==sha(obj)=='8530482c0f7c1ff7d485f6db03a559b5c6b34daec62881ee14c57429269af98d';pins[name]=row['object_sha256']
 elif i==1:assert not any(t in log for t in ('error:','warning:','sorryAx')) and row['object_sha256']==sha(obj)=='a248fb6a7868d4bcc445c5c2d93cfe010ec9c676ae9cda2e0d351f8677004b73';pins[name]=row['object_sha256']
 elif i==2:assert not any(t in log for t in ('error:','warning:','sorryAx')) and row['object_sha256']==sha(obj)=='ae79f7dd14617e237af6c37cfd6c8dd1184c633f45d88c2ac62eeb37d53df877';pins[name]=row['object_sha256']
 elif i==3:assert not any(t in log for t in ('error:','warning:','sorryAx')) and row['object_sha256']==sha(obj)=='766d173fe48aa157a4552c446c7b38a352e94ccf1f180dfbfb19165a5262a47e';pins[name]=row['object_sha256']
 elif i in (4,5):assert not any(t in log for t in ('error:','sorryAx')) and row['object_sha256']==sha(obj)==['b3fca5f710e16bbc2190aa2af9c1470af5cf9afed04f8a383c5ac9ba22edfdd5','caeb2def2c4bb8298be3d182d103d3b33645060c533a4c5163c21cbf3fe07218'][i-4];pins[name]=row['object_sha256']
 elif i==6:assert not any(t in log for t in ('error:','warning:','sorryAx')) and row['object_sha256']==sha(obj)=='3968fbdf09921ce0c9c953628c09256fc9d35e3a87bef65e97004d1ced9d02f2';pins[name]=row['object_sha256']
 elif i==7:assert 'error:' not in log and 'sorryAx' not in log and log.count('warning:')==2 and row['object_sha256']==sha(obj)=='063888a34e001134cebe2d18313d8698b718b2eaabe677dc54c9def601c981dc';pins[name]=row['object_sha256']
 elif i==8:assert not any(t in log for t in ('error:','warning:','sorryAx')) and row['object_sha256']==sha(obj)=='51bd1af9597d6f10ff65de41c1bb0d61e64dd2be1dfd7f500a130cf7122d1796';pins[name]=row['object_sha256']
 else:assert not any(t in log for t in ('error:','warning:','sorryAx')) and row['object_sha256']==sha(obj)=='9a6b06bc65ed8b3cfc17de55baf2409f955a5cbd80d990096369fdd20ea3106b' and all(t in log for t in ('other_sum_degree_le','na_square_degree','combined_degree')) and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==3
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':63895,'outer_exit':0,'successful_children':10,'guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'explicit axis combined sum degree 96 under p0 nonzero; seed binding/full lower separate'},indent=2,sort_keys=True))
