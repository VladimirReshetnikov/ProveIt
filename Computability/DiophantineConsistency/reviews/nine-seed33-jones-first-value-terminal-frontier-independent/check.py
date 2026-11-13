#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-first-value-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-first-value-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='0f1dcf5fb382bb3e4c0c66a2dca2f7296308f185d9ad526753239737ac89570c' and sha(A/'outer-terminal-author-record.json')=='6ff8a4771f92ddadc6cdfe0ba98ff494cb030e8ce5647f2e97186206cd7e5f0d';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(52036,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1061 and s['runner_sha256']==sha(P/'run.py')=='ee82a6791e8b5ca4379d791047f6b50d376495af98e92c5febc9ca173f9847bf';r=s['rows'][0];n='Sign33MacroPrefixFirst';assert r['module']==n and r['source_sha256']=='d47d077244dbb46ebc3a63256196118da254693ed6ac0e42319b5eecc4ab2072'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='b57d5998561670667f12cb03533001d0285e366931dd998fe649ff74dec8d1ef'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
for mod,h in {'Sign33MacroPrefixes':'418296ec903c9f956e982ea1126a2ce8e92cbfed70c7095b0af782dc8d8b3516','Sign33MacroCuts':'10a3693fb7bbc5fe5798d3db28b9573b7d54ad4a1e363777e915729c1a69f65e'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='9178869e6e53736c7f16628fdedf36d68f05152ba7528a7c604b45e5ca117aec' and 'warning:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33MacroPrefixFirst.first_prefix_value' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
review=D/'reviews/nine-seed33-jones-first-value-prelaunch-frontier-independent/check.py';assert sha(review)=='76176d9cbf9bf720468e40a8b5b861a420bb096740438452785bf77df1f6bd85';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':52036,'guard_slots':150,'overlay_links':1061,'scope':'d1 short-prefix value only; no full recipe/JSON semantic equality'},indent=2,sort_keys=True))
