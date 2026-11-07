#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-endpoint-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-endpoint-retry01-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='8b7490adbdecd01e9d23d3a8978c72d38deb5ef97d931ca1120627acdf2d7003' and H(A/'outer-result.json')=='df761ab2d8b8ff46be059a5a07948b6237403b8bc4057db31d51e788a2b5d98a';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'],o['state_sha256'])==(67880,1,H(A/'state.json'))
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign26DirectNative')" and s['runner_sha256']==H(P/'run.py')=='adada33b8af36074033fca06ecdd345b853b2b24e74dbcfedbccd730bd50b49b' and len(s['rows'])==1 and len(s['overlay_links'])==1366
r=s['rows'][0];n='Sign26DirectNative';assert r['module']==n and r['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean')=='582aed56a2f0effc6f97b95929abc574dec4d2151c5ef06168a11e4b9668d277' and len(r['direct_guard'])==150 and 'object_sha256' not in r
for k in ('deps','compile'):
 v=r[k];assert v['exit']==(0 if k=='deps' else -6) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and H(A/f'{n}-{k}.txt')==H(O/f'{n}-{k}.txt')==v['log_sha256']==o['logs'][f'{n}-{k}.txt']
assert r['compile']['peak_session_rss_bytes']==2937425920 and 'lean::memory_exception' in (A/f'{n}-compile.txt').read_text() and "excessive memory consumption detected at 'interpreter'" in (A/f'{n}-compile.txt').read_text()
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign26DirectPolynomialBridge','6f528a24eb7309ad9cea14501f0160ea5c092d9b4c2bf6908a1e6b83aee2acc3'),('IPRAExpressionNative','9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
for n in ('Sign26DirectNative','Sign26DirectStandard','Sign26DirectTranslated'):assert not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
pre=D/'reviews/nine-sharing-sign26-endpoint-retry01-prelaunch-frontier-independent/check.py';assert H(pre)=='f8fcb7143c37f91e6d39e62c9893b2b7eaeed881ad1c3c56d2b48061375a056b';up=D/'reviews/nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(up)=='fd473ee75a9b02210da1c3d6d9b57d4fac253bfca1b64bae131fea5b009abd6e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'CONFIRMED_FAILURE','author_session':67880,'deps_exit':0,'compile_exit':-6,'monitor_stop':None,'sampled_peak_rss':2937425920,'unrun':['standard','translated'],'scope':'no endpoint theorem; precise interpreter trigger unknown'},sort_keys=True,indent=2))
