#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-current-source-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-current-source-iff-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='f63796abaa97d61d9125b8929cbeb0056e0e3db117487eb17f6a755d2ff78565' and H(A/'outer-result.json')=='80cd40737380376576a28f6bb37fd17b1c91e0b286c049e0c942c01e4d319278'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1311 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(16022,1) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='79ffeeaa57b6aca316ea6b3609b9bfb91606d0d153e48b9b1507dd19fb77dbad'
r=s['rows'][0];n='Sign28CurrentSourceIff';assert r['module']==n and r['source_sha256']=='fb7e0570ce92707814417ecc10dffe1380ebcb7b60e95abd78c0c3026ba64254'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',-6)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
assert r['compile']['peak_session_rss_bytes']==2939822080 and r['compile']['rss_limit_bytes']==4294967296 and 'lean::memory_exception' in (A/f'{n}-compile.txt').read_text() and 'interpreter' in (A/f'{n}-compile.txt').read_text() and 'depends on axioms' not in (A/f'{n}-compile.txt').read_text()
assert 'object_sha256' not in r and not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign28CurrentSeedIff','21e5019d1429b95202aee5b03c2a422b09f7eb28876651fdd5f5a8f651292827'),('Sign31CurrentSourceIff','731041e2ed7302a0e2cb9fc0b8264be3195cd320ef6ccde407239ba57cd3d334')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-current-source-iff-prelaunch-frontier-independent/check.py';assert H(review)=='5a84c628855c7f8f3f086816e5c90508e8f2b5558233d03fec81d757674d77f7'
survey=P/'union-survey.py';assert H(survey)=='a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':16022,'outer_exit':1,'lean_exit':-6,'peak_sampled_rss_bytes':2939822080,'guards':150,'links':1311,'scope':'no successful candidate theorem or whole-run final postflight'},sort_keys=True,indent=2))
