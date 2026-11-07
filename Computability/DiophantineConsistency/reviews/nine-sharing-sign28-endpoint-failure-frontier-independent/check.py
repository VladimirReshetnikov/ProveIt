#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-endpoint-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-endpoint-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='406bf7eee5ee07ccb6c652f7a4f4736950a7f43408b2e21a031ac62288f177ab' and H(A/'outer-result.json')=='61e88f46f35895f7bfc19f2c7db3267edae886e9a82ba810d3c84566cbaa0b0b'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1326 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(57672,1) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='3f6c310edd5b967976a0c9dcbd0f73fb19bf54a7d5982765b9cf2439b6efe620'
r=s['rows'][0];n='Sign28DirectNative';assert r['module']==n and r['source_sha256']=='156948d22507371928b7e506383f54f75aee3f22aeb038cf815f4730eadaec5b'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',-6)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
assert r['compile']['peak_session_rss_bytes']==2937425920 and r['compile']['rss_limit_bytes']==4294967296 and 'lean::memory_exception' in (A/f'{n}-compile.txt').read_text() and 'interpreter' in (A/f'{n}-compile.txt').read_text() and 'depends on axioms' not in (A/f'{n}-compile.txt').read_text()
assert 'object_sha256' not in r and not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign28DirectPolynomialBridge','211972881dab16d1bb9be9c457b18a0e48b698be5199bdf2918d781d5e06ab07'),('IPRAExpressionNative','9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-endpoint-prelaunch-frontier-independent/check.py';assert H(review)=='e2464bf2c2428bb1672191acbeddd9299e5b6aa7ce634d33ec158252a9505aa2'
survey=P/'framework-survey.py';assert H(survey)=='20bceb0b7631d230eac91deb2778690edb90a6d72c4af61a07e2bc4edc97c9a6';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':57672,'outer_exit':1,'lean_exit':-6,'peak_sampled_rss_bytes':2937425920,'guards':150,'links':1326,'scope':'native stage failed; later endpoint stages and final postflight unrun'},sort_keys=True,indent=2))
