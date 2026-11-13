#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint33-41-gprime-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint33-41-gprime-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='0e3b75909e377a5541202bd6c4572cd686419d52a60381595859520f7557d141' and H(A/'outer-terminal-author-record.json')=='875afed8993572353932353e8778311beebabfafd6cc7fc7d4264ed4a5fe900a';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(53036,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1144 and s['runner_sha256']==H(P/'run.py')=='2497374e9b1756deb436cf09027245866c652e9b64b482b518e8c5d33c4450ba';names=['Sign33MacroGprimeValue','Sign33MacroGprimePath'];objs=['5e8d995dad7a155629ec328a64013b7ea255ea86af89e4287d46039f99d48c21','08be347969b66102842a2a12d9a6d01f84b325cc0a076c06dd75a00d383c12a4'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroFPath':'0986f9676c54a98490a592bd444006c7ad597044f44135cee49664aafd058b39','Sign33MacroDependentGprime':'1875c457eed36115573a42823b353f51521ca3a17ad62ba1e17e2af6b701b46a','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointGprime.path33_34' does not depend on any axioms" in log
 for th in ([['d32_A_value','d33_Gprime_value'],['lookup33_34','d41_Gprime_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointGprime.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint33-41-gprime-prelaunch-frontier-independent/check.py';assert H(pre)=='c6148f9c0b17d4b216b6d20615fba1acc26aacaadac6d9ff9a6deb4879bec7df';up=D/'reviews/nine-seed33-jones-checkpoint32-41-f-terminal-frontier-independent/check.py';assert H(up)=='17a85a79deb8593bbd52aae352e9d47437af2b9fa56eac85e2604951234e0a9b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':53036,'stages':2,'guards':300,'links':1144,'scope':'Gprime values d33/d41 and d33→d34 lookup only; no full output semantics'},sort_keys=True,indent=2))
