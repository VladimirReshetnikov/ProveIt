#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-first-preservation-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-first-preservation-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='5cdc6fa7d05ef113f2abbd427f33498462ead3088fc0bb5995a30c323ba6086d' and sha(A/'outer-terminal-author-record.json')=='7f340e14308ab9be29296e2a04cef931fbf94d10de0aa0ba9494462adcaf14d5';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(5721,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1062 and s['runner_sha256']==sha(P/'run.py')=='4716caf053d326bf90ad72a011f5c6651f030b640df6d80593f1b6e687b3e4e8';r=s['rows'][0];n='Sign33FirstPreservation';assert r['module']==n and r['source_sha256']=='001889150e87deefe92450cbfbe93a3b887b2ce02a86e1c0b53fb12a25208b9a'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='0fb688f47cc10c6c9af772e6f5e588af70cb1991b662bce008f9f740f9c96f89'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
v=r['dependencies']['DiophantineConsistency.Sign33MacroPrefixFirst'];assert v['sha256']=='b57d5998561670667f12cb03533001d0285e366931dd998fe649ff74dec8d1ef' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='04952b0106c85b12a450311352b7e012216448333aee1a3dbc7b5382c0a59e48' and 'warning:' not in log and 'sorryAx' not in log
for th in ('d45_first_eq_d1','recipe_first_value'):assert f"'DiophantineConsistency.Sign33FirstPreservation.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
review=D/'reviews/nine-seed33-jones-first-preservation-prelaunch-frontier-independent/check.py';assert sha(review)=='396eae9748971d18bbe08b8a1bced141ef6b3353128f12db77f9403639ed3a61';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':5721,'guard_slots':100,'overlay_links':1062,'scope':'full-recipe first entry only; no output semantic/JSON equality'},indent=2,sort_keys=True))
