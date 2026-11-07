#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-current-source-iff-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-current-source-iff-retry01-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='dfc94dbdc92becb9dc3971a1a999461f60fee832203f55371be933c5acfa9f93' and H(A/'outer-result.json')=='f80fcf0add0d96a2003b5230b3d5c7f0f15060c3fdfb95f0e56b782b4567005b'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==2 and len(s['overlay_links'])==1311 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(36209,1) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='8c65ffe92373f0b853119543e475fea5cb50d2f19d0863f75bf3b5fbb3b8beb0'
r=s['rows'][1];n='Sign28CurrentSourceIff';assert r['module']==n and r['source_sha256']=='cbb782e06e689edc89ec29350c2e4615833d9894524a75c64407a4e147369707'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',-6)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
assert r['compile']['peak_session_rss_bytes']==2938318848 and r['compile']['rss_limit_bytes']==4294967296 and 'lean::memory_exception' in (A/f'{n}-compile.txt').read_text() and 'interpreter' in (A/f'{n}-compile.txt').read_text() and 'depends on axioms' not in (A/f'{n}-compile.txt').read_text()
assert 'object_sha256' not in r and not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign28CurrentConsIff','2f7b33d5954dbc16bc528c98a3758954232304ad23f1121366881e307d74100b'),('Sign31CurrentSourceIff','731041e2ed7302a0e2cb9fc0b8264be3195cd320ef6ccde407239ba57cd3d334')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
first=s['rows'][0];fn='Sign28CurrentConsIff';assert first['module']==fn and first['deps']['exit']==first['compile']['exit']==0 and first['object_sha256']=='2f7b33d5954dbc16bc528c98a3758954232304ad23f1121366881e307d74100b'==H(O/'lib/DiophantineConsistency'/f'{fn}.olean') and len(first['direct_guard'])==100
assert first['source_sha256']==H(P/'src/DiophantineConsistency'/f'{fn}.lean')==H(O/'src/DiophantineConsistency'/f'{fn}.lean')
for phase in ('deps','compile'):
 v=first[phase];assert v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{fn}-{phase}.txt')==H(O/f'{fn}-{phase}.txt')==v['log_sha256']==o['logs'][f'{fn}-{phase}.txt']
for path,v in first['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=first['dependencies']['DiophantineConsistency.Sign28CurrentSeedIff'];assert v['sha256']=='21e5019d1429b95202aee5b03c2a422b09f7eb28876651fdd5f5a8f651292827' and first['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=(A/f'{fn}-compile.txt').read_text();assert log.count('warning:')==1 and 'unusedSectionVars' in log and 'sorryAx' not in log
for th in ('exists_cons_iff','seed_cons_iff'):assert f"'DiophantineConsistency.Sign28CurrentConsIff.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-current-source-iff-retry01-prelaunch-frontier-independent/check.py';assert H(review)=='77b30e9364d8fb3e4d9b4f5d4133aa3cb39fc758030275cedd30155130373361'
survey=P/'union-survey.py';assert H(survey)=='a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':36209,'outer_exit':1,'lean_exit':-6,'peak_sampled_rss_bytes':2938318848,'guards':250,'links':1311,'scope':'successful cons-form stage only; source iff failed, no whole-run final postflight'},sort_keys=True,indent=2))
