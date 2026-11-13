#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-vars-cd-rad-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-vars-cd-rad-staged-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='86bc4ff3e9b0c724b582f16576e199f1c0caac25d768ced202d615b700e51f17' and H(A/'outer-terminal-author-record.json')=='d15fcfc208d8083bc7d37a3e1a4d11fe3f2516137adbbf992d744ee0d83868e5';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(35966,0) and H(A/'state.json')==H(O/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1168 and s['runner_sha256']==H(P/'run.py')=='9d7822ba5cffc55e421fe115f146fa8693931e9f67e7168aa51acf3418784e98';assert H(P/'source-manifest.json')=='4b92a7929b1744345771bbb02bed58bfd75e51472639015c18f5b923da168595';manifest=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroVarsBd':'5134925336ba3fcc50d8ae49922e49f048e347dce85fc9079428ff812904ade8'}
names=['Sign33MacroVarsCd','Sign33MacroVarsRad0','Sign33MacroVarsRad1'];theorems=['d41_Cd_eq_dvnd','d41_A0_eq_rad0','d41_A1_eq_rad1'];objs=['1de4418f943dc801bcf134bd2b0badcbaaeec7bab7684cc438406a6d4dc6e6d6','b6f41c0ae6edca047ad9c13788ea753789ff8ba8841a9d4dfd83ac3bfc5c8ed9','d6a64e2179481caeed173f1fe719dc456b06808050687c99a7b61bf44e30aa24']
for r,e,n,th,obj in zip(s['rows'],manifest,names,theorems,objs):
 assert r['module']==n and e['module']=='DiophantineConsistency.'+n and H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean')==e['source_sha256']==r['source_sha256'] and H(O/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256']==obj and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and v['rss_limit_bytes']==4*1024**3 and v['host_floor_bytes']==10*1024**3 and v['timeout_seconds']==120 and H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert all(t not in log for t in ('warning:','sorryAx','error:')) and th in log and '[propext, Classical.choice, Quot.sound]' in log;pins[n]=obj
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
up=D/'reviews/nine-seed33-jones-vars-bd-terminal-frontier-independent/check.py';assert H(up)=='32bab5f50f326c17c0b51ae13d91db78a9fcfe7f698a9d490069ec7caa306bcb';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
survey=P/'values-survey.py';assert H(survey)=='ad5a6325247e64dabd6b15c271db6a4163633145acb6381c45d4fad4c869e8fe';x=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,text=True,timeout=180);assert json.loads(x.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':35966,'stages':3,'scope':'Cd=dvnd and A0/A1=rad0/rad1 in symbolic RingVars, with opaque rank; no full named evaluator/external binding'},indent=2))
