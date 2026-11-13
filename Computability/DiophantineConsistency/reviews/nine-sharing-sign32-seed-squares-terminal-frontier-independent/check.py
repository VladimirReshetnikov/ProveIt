#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-seed-squares-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-seed-squares-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='c5686add774156ad8156cbff8d7619f8eb9dba5c8100a2b58b48b8169def46e0' and sha(A/'outer-result.json')=='652909ed127df282440f34e4bc9692f38b017a44c1494641f336f925322740e0'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(43277,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==sha(P/'run.py')=='05a098974e1804b237fd1cf0c9e4d6ca86a6193479457957d1a2dcba283301a5'
objs=['5a502010b0195d31061c2545cfaab7608fb25417a982114e1fb3923690c38bcf','dcf5d8bb132337b5fcdbbcee6b9aac3a9d5a020cd7191be983a67628af43e850']
expect=[('SharingSeed32Sextic','83ca02c43152569d1145e32052de74f60e840c16b15e13a55800508fc2c8b0b3',100,{'NineFreshJones':'9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df'}),('SharingSign32Squares','d90b685606af0bb4bfd304748ad28d9aa559a63f5d20a20cdf7645bb77b81b44',150,{'SharingSeed32Sextic':objs[0],'SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42'})]
for row,obj,(name,source,count,producers) in zip(s['rows'],objs,expect):
 assert row['module']==name and row['source_sha256']==source and row['object_sha256']==obj and len(row['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=row[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 if name=='SharingSign32Squares':assert re.search(r"'DiophantineConsistency\.SharingSign32Squares\.seed_zero_iff_residuals' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 else:assert log==''
 for mod,h in producers.items():
  v=row['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and row['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in row['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-seed-squares-prelaunch-frontier-independent';assert sha(R/'check.py')=='fb01a24b8939887c0cf4bed9e66e3bb472102500c0536703d4797d14bd35d340' and sha(R/'result.json')=='003f15c8a6032c0d257279bbb6c6f2ff39a2a89018b1bae6809dae7900b81a3a'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':43277,'stages':2,'guard_slots':250,'overlay_links':1057,'scope':'same-valuation sign32 seed zero iff all 23 residuals zero in IΣ₁ models with symbolic integer ports; no Lean replay or 32↔33 bridge'},indent=2,sort_keys=True))
