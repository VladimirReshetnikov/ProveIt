#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-direct-ipra-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-direct-ipra-retry01-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='cafb98940ef713e8a29aab450bd55472feb7c16f133afb3ecbb6da32a9031aa0' and sha(A/'outer-result.json')=='0b26d9a671690116538d10454b811b833c729a15f3d5918896154d14af7a4eb3';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(76962,1) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==6 and len(s['overlay_links'])==1298 and s['runner_sha256']==sha(P/'run.py')=='90febb9284bb0ec2421bcd7e2e347d6c1fc2721174309f85bc8a38bbcb2d3645';names=['Sign31AbstractExpressionDef','Sign31AbstractExpressionEval','Sign31CurrentExpressionDef','Sign31CurrentExpressionEval','Sign31CurrentExpressionSource','Sign31DirectIPRA'];objects=['209ac724b2c9e57bc7f62f1ef61df0b2d019f4d5d0522a934605e61d22d48464','57a4cf8d989b694ea835b0a70445cade96bc2f1c59998c2fc3733894e58d87f7','9e70214fce038cf543788ac4bce87a73446ad6410506a5287ba8c9fbdf952aaa','eedb576a31f8255f9b556f5edb67e4e0631ede9a19b744be502f38fb8a7e60be','8e6bf650153fe5ecb5ac162d2e9550835f084af468c734b472af0308c94b58a9'];m=json.loads((P/'source-manifest.json').read_text())['rows'];guards=[150,100,150,100,150,250]
for i,(r,n,entry) in enumerate(zip(s['rows'],names,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==guards[i]
 if i<5:assert r['object_sha256']==objects[i]==sha(O/'lib/DiophantineConsistency'/f'{n}.olean')
 else:assert 'object_sha256' not in r and r['compile']['peak_session_rss_bytes']==2940682240
 for phase,code in [('deps',0),('compile',0 if i<5 else -6)]:
  v=r[phase];assert v['exit']==code and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 for mod,rec in r['dependencies'].items():
  if mod=='Init':continue
  assert r['direct_guard'][rec['path']]=={'sha256':rec['sha256'],'realpath':rec['realpath']}
  local=mod.split('.')[-1]
  if local in names[:i]:assert rec['sha256']==objects[names.index(local)]
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 if i in (0,2):assert log==''
 if i in (1,3,4):assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in ' '.join(log.split())
 if i==5:assert sha(A/f'{n}-compile.txt')=='48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a' and 'lean::memory_exception' in log and "at 'interpreter'" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign31-direct-ipra-retry01-prelaunch-frontier-independent/check.py';assert sha(review)=='c48da6539581a559c3304e123e881bdf8f44f549a9152ab701b7c5605cece097';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','author_session':76962,'successful_stages':5,'failed_stage':'endpoint module -6 interpreter memory exception; internal declaration unknown','sampled_peak_bytes':2940682240,'guard_slots':900,'overlay_links':1298,'scope':'five completed expression/evaluation/source stages; no endpoint or final postflight'},indent=2,sort_keys=True))
