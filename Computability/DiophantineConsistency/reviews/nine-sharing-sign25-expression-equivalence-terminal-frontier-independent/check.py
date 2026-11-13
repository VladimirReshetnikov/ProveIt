#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-expression-equivalence-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-expression-equivalence-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='fed307cd8b6e8aeae4740b47cb3d68fbc5b3dbc99d166fe82be6a977a61167ed' and H(A/'outer-result.json')=='7f52bc1a5dcab605e1daa106195b979c1aa803cfccca39bbd73e3086ec4bae5b';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(18849,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1078 and s['runner_sha256']==H(P/'run.py')=='83cef530879d27e5f1b95bcb0dd87a9e16b3084a66743602602846308f960ee7';r=s['rows'][0];n='Sign25ExpressionEquivalence';assert r['module']==n and r['source_sha256']=='c086e008252df8e384d4ce9641d049f5c921a37e704b313ea9ffd55571f81dca'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='37ed3cc6346eb68df0fb8d4bec90edd66801cb9ba61f25301811202e1c141683'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign25SeedExistential','ffc2393e2eae606147b1de0eb24c1a6c38c28fbadff569644ee5e80d23736c2d'),('Sign25CurrentExpressionEval','5ad9879f6ceac9321466e21521402c8a6444f2adcaacb98f38eaedfbb0ffe081'),('Sign26CurrentExpressionEval','93eb07957c23cc42b56a0fd5b513495c04e8d6e8beba3da6c8e5b2c8a2232e9e')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert log.count('warning:')==1 and 'automatically included section variable(s) unused' in log and 'sorryAx' not in log and 'error:' not in log
for th in ('exists_cons_iff','zero_exists_iff'):assert f"'DiophantineConsistency.Sign25ExpressionEquivalence.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-expression-equivalence-prelaunch-frontier-independent/check.py';assert H(pre)=='f36d266da39e3426999eaff80d4d5f8eeefe1bad4d44623deb53584ed7ee4450';
for name,h in [('nine-sharing-sign25-seed-iff-terminal-frontier-independent','cf70b18afea58dacc013b8bfa3a3b6e4aca1e58da78abc53d1dc5a11447eecca'),('nine-sharing-sign25-expression-eval-terminal-frontier-independent','adb2983992b6c7c3ef4c0991c6292336f2ec3ad4288ae9a9a8dee30bcf48c7f1'),('nine-sharing-sign26-expression-eval-terminal-frontier-independent','cfb5f67ddef456f6e82061ee17a4dd1b17d90ee2f8147207fe465085d46ef0b4')]:
 up=D/'reviews'/name/'check.py';assert H(up)==h;subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':18849,'guards':200,'links':1078,'scope':'sign25/sign26 direct-expression zero-existence iff over IΣ₁; no source endpoint'},sort_keys=True,indent=2))
