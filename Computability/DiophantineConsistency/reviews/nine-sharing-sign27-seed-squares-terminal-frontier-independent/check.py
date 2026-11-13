#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-seed-squares-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-seed-squares-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='a7a6217c44a8f70f18d8ed06e5bb29d336ff0bb7efadfb6ef6694e987e248dbe' and H(A/'outer-result.json')=='c16294e788588e48a735eda2fb1abf66bdf15d8133a43dccb0b0ecf73c3aeaa0';s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(78774,0) and o['retained_state_sha256']==H(A/'state.json') and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==H(P/'run.py')=='91f0c3e857dda29836ab4c5f364d4d1d38e161450096d2a5a245832377e73f18'
names=['SharingSeed27Sextic','SharingSign27Squares'];objs=['8313b5570e835ea52d66d7c33c64514d511173efcb1dab0166e701af3798e356','b7f2a083a1a7a81d57b6fafe67670d8065f43f57396cc2503a38bda0f078bd40'];deps=[{'NineFreshJones':'9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df'},{names[0]:objs[0],'SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42'}];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod,h in deps[i].items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 if i==0:assert not log
 else:assert "'DiophantineConsistency.SharingSign27Squares.seed_zero_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign27-seed-squares-prelaunch-frontier-independent/check.py';assert H(review)=='41d2fb64af9a94757f7102821555129d4b514edbb88c858e446288ce0861b7e6'
plan=D/'research/nine-sharing-sign27-lean-bridge-plan/README.md';t=plan.read_text();suffix='\nThe [independent source review](../../reviews/nine-sharing-sign27-lean-bridge-plan-frontier-independent/README.md) passed for this plan and the accompanying source-only syntax/bridge draft.\n';assert t.endswith(suffix) and hashlib.sha256(t[:-len(suffix)].encode()).hexdigest()=='b5698aeb200a37fe72066d38f6a2e3e99c20a141fe52e118a6edc72fc7e905d5'
for script in ('check.py','check_bridge.py'):
 f=D/'research/nine-sharing-sign27-sextic-lean-draft'/script;subprocess.run([sys.executable,'-I','-S','-B',str(f)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':78774,'stages':2,'guard_slots':250,'overlay_links':1057,'scope':'symbolic Fin28 syntax and 18-residual square iff only; historical plan replay caveat'},sort_keys=True,indent=2))
