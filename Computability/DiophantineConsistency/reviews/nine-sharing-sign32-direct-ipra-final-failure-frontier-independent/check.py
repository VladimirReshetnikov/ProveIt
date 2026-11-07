#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-final-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-direct-ipra-final-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='148101c02f0b631ed27c0b6588ab3bf120eac27ec7cce0568af0ba8930871511' and sha(A/'outer-result.json')=='a220de18250b2893c2b4a67bf5e533ee33c53e83edcf1a726eef1de75914ab14';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(71710,1) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==2 and len(s['overlay_links'])==1290 and s['runner_sha256']==sha(P/'run.py')=='911f7cbc5ead587cd97d1335606aaf76681348d1fd744d7c90a0a87965b273bc'
names=['Sign32CurrentExpressionSource','Sign32DirectIPRA'];obj='e1f97c454d60009f2015aa69d048f328f3d25dde74326f068394debaa4b94876';m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,entry) in enumerate(zip(s['rows'],names,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==[150,250][i]
 if i==0:assert r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean')
 else:assert 'object_sha256' not in r
 for phase,code in [('deps',0),('compile',i)]:
  v=r[phase];assert v['exit']==code and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 for mod,rec in r['dependencies'].items():
  if mod=='Init':continue
  assert r['direct_guard'][rec['path']]=={'sha256':rec['sha256'],'realpath':rec['realpath']}
 if i==1:assert r['dependencies']['DiophantineConsistency.Sign32CurrentExpressionSource']['sha256']==obj
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
one=(A/f'{names[0]}-compile.txt').read_text();two=(A/f'{names[1]}-compile.txt').read_text();assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in ' '.join(one.split()) and 'warning:' not in one and 'sorryAx' not in one;assert sha(A/f'{names[1]}-compile.txt')=='92afa24d5a221c42f4a66bcd3fda472cb12e84967d8c40990809ff3618cedb4e' and 'error: Type mismatch' in two and 'ObjectCurrentEquation2011.InternalZero' in two and two.count('sorryAx')==4
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','author_session':71710,'stage1':'source zero iff succeeds, standard axioms no warnings','stage2':'type mismatch, four error-contaminated sorryAx reports; no object','scope':'no endpoint or final whole-run postflight; author-recorded outer exit'},indent=2,sort_keys=True))
