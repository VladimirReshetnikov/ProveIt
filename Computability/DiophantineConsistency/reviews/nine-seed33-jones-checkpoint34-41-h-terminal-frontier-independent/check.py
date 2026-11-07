#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint34-41-h-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint34-41-h-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='d005cc3f6c794df8160380fd4dedb544b92751f0ce7d791ed97a95ad8de98c5b' and H(A/'outer-terminal-author-record.json')=='8df133174626e1c193c0d0f07e1648fd3e6a2c794291b3c8e05a280cb75d4f09';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(93488,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1146 and s['runner_sha256']==H(P/'run.py')=='aef426e38733a4964df7ebdb3e2de6ef752dd663658abfa42501c5a74f1b33d2';names=['Sign33MacroHValue','Sign33MacroHPath'];objs=['f87721f22da0a54cf35fd7b5600cbc80d5f8e1666527145313255873d8ff5149','6a2b366e725ff74521b0334321b1ff94a5266088edbc1c77b533b26eff8253d9'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroGprimePath':'08be347969b66102842a2a12d9a6d01f84b325cc0a076c06dd75a00d383c12a4','Sign33MacroDependentH':'5b5bf4045f0e4f151681765d3339d847559f324ee47ebc37fc046b120165ce01','Sign33MacroLive18Group04':'05ef726ab4c0aecb12d36ba7a0309a8875e335a387ebf4ea0810572beb9df0ec','Sign33MacroPrefixInputsB':'1fa27bad80c2a5df777dd57235777d762bc4e7018ab9b830eb447467dc300ba8','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[250,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 for th in ([['d33_j_value','d33_Bprime_value','d34_H_value'],['d41_H_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointH.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint34-41-h-prelaunch-frontier-independent/check.py';assert H(pre)=='a6f41fe4fc33d5d7aa32cd94ce97be9de6dc7c64f299553fa6f3a74fabfffe5f';up=D/'reviews/nine-seed33-jones-checkpoint33-41-gprime-terminal-frontier-independent/check.py';assert H(up)=='e9f0341efd830145bc7efcc2d1a15ea9358c9c5aa14ec47b0666657b7f480d15';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':93488,'stages':2,'guards':400,'links':1146,'scope':'H values d34/d41 only; no full output semantics'},sort_keys=True,indent=2))
