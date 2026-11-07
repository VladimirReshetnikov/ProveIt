#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-named-equality-retry01';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-named-equality-retry01-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='a22aeb4f1ee2cc4d02a797405f08d10b439f8c654755296ae98759ff5dae0da1' and sha(A/'outer-terminal-author-record.json')=='3d4cd9e6c26e78e68dc690f55a28d9934dc1e0870cf0c21eda86cb0315391c43';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(78976,1)
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1283 and s['runner_sha256']==sha(P/'run.py')=='0e3372d764049b7de2bd5a2ba9a23cdbc5c8bfcf933b645557ebaedc336af65e'
r=s['rows'][0];n='Norm38MacroNamedVars';assert r['module']==n and r['source_sha256']=='0618e50c2d3f687e53ca330439e50920dd7880760284b5569c25b691cfd648bb'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150 and 'object_sha256' not in r
for phase,exit in [('deps',0),('compile',1)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
for mod,h in {'Norm38MacroVarsOutput':'068b76a14eb12512b8a83b72feb31be24e2a8a21977bc76998c3b52ff4b1d4b5','Norm38NamedFormula':'f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='78b1d99f8cd382c89ec86e54c83c98f091afbf4d5ebffb1f5042d3bf56871c0b' and 'error: Type mismatch' in log and 'Fin.cons' in log and 'sorryAx' in log
print(json.dumps({'status':'PASS_FAILURE_AUDIT','session_author_record':78976,'scope':'first-stage dependent Fin.cons codomain type mismatch; sorryAx contaminated report; no object, second stage or postflight'},indent=2,sort_keys=True))
