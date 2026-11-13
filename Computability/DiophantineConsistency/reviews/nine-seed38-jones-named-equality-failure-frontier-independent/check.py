#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-named-equality-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-named-equality-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='ee283f4f1ff98bfd3fbb075442c3fcb8cc8e7ccc7fbee812368040ff6ceccc39' and sha(A/'outer-terminal-author-record.json')=='2b140fafbc89231e89b8c4824c6037b7328723d01a52830d9f160cccfbcae7de';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(89988,1)
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1283 and s['runner_sha256']==sha(P/'run.py')=='ec56991abaea43920b0c54191b97d49a8a1c56c1463f91a8d47dc5ab6d436969'
r=s['rows'][0];n='Norm38MacroNamedVars';assert r['module']==n and r['source_sha256']=='7b2c1bf1208802cf92a6d9e795104abbff952cfabeac978f1afa8c97289e2e5b'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150 and 'object_sha256' not in r
for phase,exit in [('deps',0),('compile',1)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
for mod,h in {'Norm38MacroVarsOutput':'068b76a14eb12512b8a83b72feb31be24e2a8a21977bc76998c3b52ff4b1d4b5','Norm38NamedFormula':'f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='1a2d0028b9e0523a2a4fb4fdb6304226a011db0ab3af0eaee96f4ac5578874c1' and 'error: unsolved goals' in log and 'Fin.cons_succ' in log and 'This simp argument is unused' in log and 'sorryAx' in log
print(json.dumps({'status':'PASS_FAILURE_AUDIT','session_author_record':89988,'scope':'first-stage unsolved finite-index and exponent normalization; one unused-simp warning; sorryAx contaminated report; no object, second stage or postflight'},indent=2,sort_keys=True))
