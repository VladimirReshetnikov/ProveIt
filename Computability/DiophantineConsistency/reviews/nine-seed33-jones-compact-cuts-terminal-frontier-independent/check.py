#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-compact-cuts-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='968ed7b4b3dc81a85d0dafcfb633dea5e033a91bd5b634d73edc8dcdb9e3b054' and sha(A/'outer-terminal-author-record.json')=='01ac90818a4e337ad18c7f531b49badd7f288d527e44c50360be5c8894af71ba';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(88083,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==sha(P/'run.py')=='61a5a2528624434c74e3154e31572a6e1cf11ab131e5f725e8a9e2c7fceb1a20';names=['Sign33MacroCuts','Sign33MacroPrefixEmbedding'];objects=['10a3693fb7bbc5fe5798d3db28b9573b7d54ad4a1e363777e915729c1a69f65e','8bf6d79a1c5313487c4b74d683480d49f73d2485f81b442c41f442223137b305'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroLanguage','9e1b3c12f306411cfc650eaf0182042ae607a81b4b75f8cc660f0daf46bea4d3') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in (['snoc_previous','snoc_last','eval_range','eval_star'] if i==0 else ['lookup','lookup_two']):assert f"'DiophantineConsistency.{n}.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-compact-cuts-prelaunch-frontier-independent/check.py';assert sha(review)=='34b4f268ce120812922077a672ba52df0ad267e22a89bba4bc11d7c0b794b4d6';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':88083,'stages':2,'guard_slots':200,'overlay_links':1057,'scope':'four generic cuts and two prefix lookups only; no concrete recipe equality'},indent=2,sort_keys=True))
