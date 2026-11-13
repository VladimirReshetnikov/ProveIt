#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-current-source-iff-retry02';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-current-source-iff-retry02-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='f3c8869fe73c5ca2f6acf262c8c856c2b3ca74124372549abff406c2d7c6bd0e' and H(A/'outer-result.json')=='aad820136968dab5b6445faa5e3715a59778d9c6423d31d32dd5b6fc3c392785'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1312 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(24903,1) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='edadada805fcb17a16f3e5cb5ae59221011c9242bbe00ba350e311adb046b4cd'
r=s['rows'][0];n='Sign28CurrentSourceIff';assert r['module']==n and r['source_sha256']=='c0e0adfac4e63ea38a0af17d7c122233cd2f6cc9c081fda23b1986cb2396c83c'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',-6)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
assert r['compile']['peak_session_rss_bytes']==2939375616 and r['compile']['rss_limit_bytes']==4294967296 and 'lean::memory_exception' in (A/f'{n}-compile.txt').read_text() and 'interpreter' in (A/f'{n}-compile.txt').read_text() and 'depends on axioms' not in (A/f'{n}-compile.txt').read_text()
assert 'object_sha256' not in r and not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign28CurrentConsIff','2f7b33d5954dbc16bc528c98a3758954232304ad23f1121366881e307d74100b'),('Sign31CurrentSourceIff','731041e2ed7302a0e2cb9fc0b8264be3195cd320ef6ccde407239ba57cd3d334')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-current-source-iff-retry02-prelaunch-frontier-independent/check.py';assert H(review)=='484c24c48c2805697c9b39ac2b4905a3d90fd29cca9da5367ddd18ce31c43071'
survey=P/'union-survey.py';assert H(survey)=='a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
survey=P/'partial-survey.py';assert H(survey)=='462acee066ec0a45fb30b682cc7d435a0b4b1414b9f8129c6f326ca3049ded8e';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':24903,'outer_exit':1,'lean_exit':-6,'peak_sampled_rss_bytes':2939375616,'guards':150,'links':1312,'scope':'no successful candidate theorem or whole-run final postflight'},sort_keys=True,indent=2))
