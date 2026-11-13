#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-current-source-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-current-source-iff-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='214196396eaa1ca0536edf65772ce03df4d03f637144683588cc768dc953f287' and sha(A/'outer-result.json')=='5c6437fc23959eb8e90dd57b3061917c66f6bdc5daca29a7ded90482de71271a';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(46181,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1296 and s['runner_sha256']==sha(P/'run.py')=='eded4160e6d5c573439a5af18bd30f47b81d468ca5e3ab5a1959e584abfd2074';r=s['rows'][0];n='Sign31CurrentSourceIff';assert r['module']==n and r['source_sha256']=='037b472c62fabdb7ac18d392ffe53615e5bb472b031fe8e006263f77fcabd76a'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='731041e2ed7302a0e2cb9fc0b8264be3195cd320ef6ccde407239ba57cd3d334'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
for mod,h in {'Sign31SeedExistential':'9f1e9a1537698844baa09d0461409f907e6d21b9396e5ab8ec35b4434fdafd64','Sign32CurrentSourceIff':'d5dce54ef8afdd6c9a55a9c4b00816bd091995a6a34b488f8f776053e627eda1'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='a1487823056679c9d2a6fbb819bb8a687c301ae7525d9631f9e3b113c76d3260' and 'warning:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign31CurrentSourceIff.seed_exists_iff_source' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
source=(P/'src/DiophantineConsistency'/f'{n}.lean').read_text();assert '∃ w : Fin 31 → V' in source and 'Fin.cons (1 : V) w' in source and '∃ u : Fin 14 → V' in source and 'CurrentWindowCarry2011.ports' in source
review=D/'reviews/nine-sharing-sign31-seed-iff-terminal-frontier-independent/check.py';assert sha(review)=='d8010c17ed2042d0b4ad1ce66f8f6aa252b17366f4083097654ea08b11397e23';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':46181,'guard_slots':150,'overlay_links':1296,'scope':'fixed current ports and leading input 1; Fin31 seed witnesses iff Fin14 current source in IΣ₁; no direct iPRA endpoint or Lean degree/JSON binding'},indent=2,sort_keys=True))
