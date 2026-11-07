#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-seed-squares-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-seed-squares-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='8caedeefbd19c335dc9098b74aec3729962248fc2d4c128b4a8aff269a081478' and H(A/'outer-result.json')=='c9bd6f02d7095922b31cd71df3b64f1eea01fbac517a45e89131209646d3abc1';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(87857,0) and o['state_sha256']==H(A/'state.json') and o['author_observed_stdout']=='PASS sign26 residual-square diagnostic'
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==H(P/'run.py')=='6a6cc8c6477be7ce730633685883b9a72635296e745776f4a84896aef61532de';names=['SharingSeed25Octic','SharingSign25Squares'];objs=['0f3cba46b15523eca6054d9399ab503e3f11160402ffd228a1fc870a33848f5a','5a019d411c6966d8420c0b57ac35c7acc8415892bb533983dfb2abe9128a7063'];pins={'NineFreshJones':'9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df','SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42',names[0]:objs[0]};m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==0:assert not log
 else:assert "'DiophantineConsistency.SharingSign25Squares.seed_zero_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-seed-squares-prelaunch-frontier-independent/check.py';assert H(pre)=='b1ca08a00ecdf98ef7b45c36a2a36cf712126d75ecf97bcc2ddfcef8d641e511';up=D/'reviews/nine-sharing-sign25-octic-lean-draft-frontier-independent/check.py';assert H(up)=='330bf6c64dd09963d4b07a2cc3e56e3510e6c442d97e05111a88146122c1ff10';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':87857,'stages':2,'guards':250,'links':1057,'scope':'sign25 symbolic seed and 16-row square-sum extraction only; no sign26 bridge'},sort_keys=True,indent=2))
