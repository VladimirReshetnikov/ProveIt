#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group01-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-group01-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='1fc219f4801743baf9f7e706360b2d510d3d7fff7c8dd7cb45a0b854841bc118' and sha(A/'outer-terminal-author-record.json')=='c1604495deeb176a1b7de30556b4d8c9e02264671d7b3bbfd5ef4efe4b6223f4';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(7933,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1062 and s['runner_sha256']==sha(P/'run.py')=='c82161a9d2a76f8d595a57a980530f80579523c3e106b71c2f0f6e37dbd9f8dc';r=s['rows'][0];n='Sign33MacroPrefixGroup01';assert r['module']==n and r['source_sha256']=='4de34e34ba44e50597c0bd4acdc6e72ed32ee06a344bec2afe1ab87da3173d17'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='d2295245406c44360fd6c219cbd16d5117b9566e855a2cf4e5e2352fdccfdbbf'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
v=r['dependencies']['DiophantineConsistency.Sign33MacroPrefixFirst'];assert v['sha256']=='b57d5998561670667f12cb03533001d0285e366931dd998fe649ff74dec8d1ef' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='04d749fa7c73b1381805837b630eee1cbac33936d0654a671a9ba7fba643650c' and 'warning:' not in log and 'sorryAx' not in log
for th in ('prefix_B','prefix_q','prefix_N'):assert f"'DiophantineConsistency.Sign33MacroPrefixGroup01.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
review=D/'reviews/nine-seed33-jones-prefix-group01-prelaunch-frontier-independent/check.py';assert sha(review)=='d0a9df94a130b9bcaafb13276687b991e51745b47c8ad238182a39611a3800cf';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':7933,'guard_slots':100,'overlay_links':1062,'scope':'d2/d3/d4 short-prefix values only; no output semantic/JSON equality'},indent=2,sort_keys=True))
