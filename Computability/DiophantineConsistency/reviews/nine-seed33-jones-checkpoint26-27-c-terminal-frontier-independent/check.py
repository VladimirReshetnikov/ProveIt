#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint26-27-c-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint26-27-c-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='a26952c075daaf2e1169d1f7cf73a8b40f8779a5f59d29858b4251b06fefacab' and H(A/'outer-terminal-author-record.json')=='04ed08e2503e0ced89f1e1106c30375a5c73002ac98726b899bc66d1d0e04891';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(37880,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1133 and s['runner_sha256']==H(P/'run.py')=='a73c0f9425a631f4842e81b3067f469ab6eee65797eb00c4bc2f24a121739e91';names=['Sign33MacroCInputs','Sign33MacroCBW','Sign33MacroCValue'];objs=['541e6900940a7c3c40a440483ba915d062afc2edc8e8c511e9340a271d2678f8','873a4aa8af4886d0f17af9bdc3f2e95350dfd1a2d4436719c654bdf84fda09f9','4adbe317020d9cee22d6e735562baa3cd21e0319067c98e66f403dcbfc0d9f2b'];ths=[['d18_b_value','d18_phi_value'],['d26_Bprime_value','d26_W_value'],['d27_C_value']];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroJPath':'14a7e6c714d2ad44a4cf3b35c66fc2202cfa61f15c0f94762aae6802d8ef4772','Sign33MacroLive18Group01':'9ad348b1432ec9acb52c84a5605cf91131d04c1c4b7f8470715298eb582d99d1','Sign33MacroLive18Group03':'3fb6663a5d3070e902df9e95f4accd0058a7ada288923837f0c1464273388364','Sign33MacroPrefixGlarge':'1887baa3203c288e248f8ee85eb0af794de72272dbde1c039a8774ebc4735e2f','Sign33MacroPrefixInputsB':'1fa27bad80c2a5df777dd57235777d762bc4e7018ab9b830eb447467dc300ba8','Sign33MacroDependentW':'923a2e06a49e01c89605bc01f9c59dedc5138cc92adf90a5a12cb7838b062f57','Sign33MacroLive18Group02':'8d4d912136b18a8d46b5904d3c1d8127e5fbafc40d62ffb25ef09a63c094b004','Sign33MacroUYInputs':'79f57b67d14168984ec8f210f813c42a8e81c105fc038fd747df05dfc97b67c8','Sign33MacroDependentC':'7d4b8010fa88f6b17f163b5e897ca76484416a2ee4c82d1e1b371f78ba6eb389',**dict(zip(names,objs))}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[300,250,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroCheckpointC.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint26-27-c-prelaunch-frontier-independent/check.py';assert H(pre)=='87815f39d9a9522f1813cdef63d5e9d4ecf9783a4180e86d9a156dcc7a6c8d31';up=D/'reviews/nine-seed33-jones-checkpoint28-41-j-terminal-frontier-independent/check.py';assert H(up)=='4016222664cc8081a8e8d45986c0237479bc70ff33781a3bedc07d48657eed9e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':37880,'stages':3,'guards':700,'links':1133,'scope':'d27 C with opaque rank and intermediate inputs only; no full output semantics'},sort_keys=True,indent=2))
