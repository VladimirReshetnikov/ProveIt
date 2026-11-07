#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint22-23-pk-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint22-23-pk-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='bafa0783c59b1392f6b91d70bf3d18631579790b72edda2b5846c18c693c2163' and H(A/'outer-terminal-author-record.json')=='71d66568e490d0ffb2207fb93fda4bfd3d762bdaa17443db0c3c99c9fcf5733b';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(9330,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1150 and s['runner_sha256']==H(P/'run.py')=='9f35a26f501a9b3b680a985237b2481baf418c2d5df7663dbc06648ea1a6153c';names=['Sign33MacroPValue','Sign33MacroKValue'];objs=['273d7b5ece738f08aa9e76f8d79066abd47d0705ed4a7a8f3c50b10cf5ab588e','c79c0fa12bf371f4d75051755faf52c6dd3e49adf0411bf5ae836eadee21d7ac'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroIPath':'b23a629ef3d1a20513930714517fec8895f9f43e228efbe77123e06617a3d7d2','Sign33MacroDependentP':'c4d38fbc81e2386b0385138277d63145f115cde5cfe5ce9b49cd12d2bf5cb02c','Sign33MacroDependentK':'d8702218c9633485b986a49cb9cb4308027648156649c3babd196f612f751174','Sign33MacroLive18Group02':'8d4d912136b18a8d46b5904d3c1d8127e5fbafc40d62ffb25ef09a63c094b004','Sign33MacroPrefixInputsA':'3cfc3529c97019bfa57f20d136eef22d4e822771b6cf2da051b5a6d9e61eacab',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,250][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 for th in ([['d22_P_value'],['d23_K_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointPK.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint22-23-pk-prelaunch-frontier-independent/check.py';assert H(pre)=='aba2d96a1d71794acf302b4bd3e4a3607bb01e1577844de2121a193df88c6857';up=D/'reviews/nine-seed33-jones-checkpoint35-41-i-terminal-frontier-independent/check.py';assert H(up)=='3b8dd8d5c2c68a084f00d7cdde8f2f08a76c7f08b4565a8aba50d48e73d340a2';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':9330,'stages':2,'guards':400,'links':1150,'scope':'P d22 and K d23 symbolic values only; no full output semantics'},sort_keys=True,indent=2))
