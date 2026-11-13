#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-remaining-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-remaining-cuts-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='450a3f5bd8412288ba00ede2ecd54906c48499004e50fb8b3d7473930ff027c9' and H(A/'outer-result.json')=='4dceddcee75ece8e734b78cef18b102e2bd096c0451e930675d4a347ac018e06';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'],o['state_sha256'])==(35318,0,H(A/'state.json'))
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1062 and s['runner_sha256']==H(P/'run.py')=='e35c28431cf4d52bdfcd7e4f90e74bfab2fbb12a120fb726c2417c3b2e59101b';names=['Sign25RemainingCuts00','Sign25RemainingCuts01'];objs=['12f0e7082fed5d2a389154a67815e1d7b9fcb89f7bbf01caaa64dddd15937949','a7c35d01deeed7d73e3d584b8a8ab2b2bd0e27f00f859548fd1a5586ebc1065e'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign25FirstCut':'e871a81de3d113a81b0df6c74fb744bf2bf4d678d7fd3a84d9579970eacbc320',names[0]:objs[0]};groups=[[1,2,3,5,6,7,8],[10,11,12,13,14,15,16]]
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert log.count('warning:')==[8,10][i] and log.count('Variable name `p` is not explicitly referenced')==[8,10][i] and 'sorryAx' not in log and 'error:' not in log
 for j in groups[i]:
  for prefix in ('old_R','new_R'):assert f"'DiophantineConsistency.Sign25RemainingCuts.{prefix}{j:02d}_row' depends on axioms: [propext]" in log
  assert f"'DiophantineConsistency.Sign25RemainingCuts.R{j:02d}_eval' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
 if i==0:assert "'DiophantineConsistency.Sign25RemainingCuts.first_eval' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-remaining-cuts-prelaunch-frontier-independent/check.py';assert H(pre)=='d5dc142e798e8224aa1f309d5202351df1e9fbd955d0e42088c3b2aa96af6796';up=D/'reviews/nine-sharing-sign25-first-cut-terminal-frontier-independent/check.py';assert H(up)=='bdd993aaa2ab6425fb1497842b5de8765d7338b81d2b9e01d7780e296dbf9b7c';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':35318,'stages':2,'guards':200,'links':1062,'row_reports':28,'evaluation_reports':15,'unused_p_warnings':18,'scope':'q3 plus 14 ell-independent transfers; no full bridge'},sort_keys=True,indent=2))
