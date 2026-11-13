#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-ordered-ring-retry01';A=P/'attempt01';O=Path('/tmp/sign26-ordered-ring-retry01-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='5e8eecb6b7e02494b212f9ed17591d5db80c6068def201d16c1bac29203428a9' and H(A/'outer-result.json')=='a336db3d9e62a8fcda4468c3ceb7225d3a334ec058a7964d6aa154071fa165e1';s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(5668,0) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='1cbb8d74ad5656334289acdb47b67dda8f5d6e15ebab19a71e588056d8d33288' and s['source_sha256']==H(P/'src/Sign26OrderedRing.lean')==H(O/'src/Sign26OrderedRing.lean')=='62f7bfe8ecf03d54da4a870c8da0a2f6941e565c60f5f7dab6618fa5f64bb58f' and len(s['direct_guard'])==80
r=s['rows'][0];assert r['module']=='Sign26OrderedRing' and r['object_sha256']=='d4ace8e8669574bc73d52462787dc7624a630f8d8429f92163de3ab20baf24f9'==H(O/'lib/Sign26OrderedRing.olean')
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'Sign26OrderedRing-{phase}.txt')==H(O/f'Sign26OrderedRing-{phase}.txt')==v['log_sha256']==o['logs'][f'Sign26OrderedRing-{phase}.txt']
log=' '.join((A/'Sign26OrderedRing-compile.txt').read_text().split());assert log.count('warning:')==2 and 'linter.unusedSectionVars' in log and 'linter.unnecessarySeqFocus' in log and 'sorryAx' not in log and 'error:' not in log;assert "'Sign26OrderedRing.congruence' depends on axioms: [propext, Quot.sound]" in log and "'Sign26OrderedRing.gap_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,v in s['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,v in r['dependencies'].items():assert s['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
pre=D/'reviews/nine-sharing-sign26-ordered-ring-retry01-prelaunch-frontier-independent/check.py';assert H(pre)=='94d359bd529f0351395ebe1e4db24c3a2ecac02bcaa2c768d40ee0e48fbbd28a';up=D/'reviews/nine-sharing-sign26-ordered-ring-failure-frontier-independent/check.py';assert H(up)=='ee7f3fc8825d6eabda29a86fd835a1c1b2ef7565c235b9a597b032e00c429cd1';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':5668,'guards':80,'warnings':2,'scope':'generic ring congruence and conditional ordered-ring nonnegativity; no model hypotheses or representative'},sort_keys=True,indent=2))
