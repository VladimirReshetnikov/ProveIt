#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-current-hypotheses-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-current-hypotheses-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='0804fe71996cf494065b75b1841dabd289c4de523b6ea0478d2cc49c9d74e2dc' and H(A/'outer-result.json')=='41c9ed4765d5da8d79d5ee8d134a131c2df8a3739b9c15024ba645a9c31e8d63';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(17653,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1063 and s['runner_sha256']==H(P/'run.py')=='62f1f551c9a11ae12fdc9fe8b96560ee85876f18f866f0ee7b1368b3ef8d256d';r=s['rows'][0];n='Sign26CurrentHypotheses';assert r['module']==n and r['source_sha256']=='91dbe9d84eacce0d441812d36cbae146b828d642ff472576588fdc70d9f1e066'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='c4692189c4b27b48777b545bfa7829f01a06916d3d7c43a4de09602752efb88c'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign26SeedGap','23e9375c793b42a99d4505557fa98c4aafbf633c7a631b047662640138a245c3'),('ArithmeticCarrierSoundness2011','fbcc145628f84d5937737fa25338a1c03098ccc228f03a9967b6691acbc096ab')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
for th in ['port0','port1','beta_ge_one']:assert f"'DiophantineConsistency.Sign26CurrentHypotheses.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-current-hypotheses-prelaunch-frontier-independent/check.py';assert H(pre)=='11df954a13a7e28e9d8942437278d4cac00fae83e4646f9ecb227cb96b69b6ac';up=D/'reviews/nine-sharing-sign26-seed-gap-terminal-frontier-independent/check.py';assert H(up)=='9a107d39ef50a60c5ea5dfe8e5b1220c8faf35d074a44e4a4b9dc793df4c7347';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':17653,'guards':150,'links':1063,'scope':'current p0/p1 casts and beta≥1 only; no seed-gap application'},sort_keys=True,indent=2))
