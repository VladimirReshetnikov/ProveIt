#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-rank-composition-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-rank-composition-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='db4826a2c3a4618815a7c23f2951dac648f4ff3ead77c09b6c23d4c8cf534e37' and sha(A/'outer-terminal-author-record.json')=='1cf0dac692fa92ed79dff029b8700421c8a5bbe0edcb69c8e2555b0f365c82fb';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(29827,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1078 and s['runner_sha256']==sha(P/'run.py')=='17847dda236f7d2ec70d9df5eb518aad631d19330829cf5869de76b681bff672';names=['Sign33MacroRankComposition'];objects=['848263c5c75e6c09c16a345ee38fa48adc8ab5883ccffd2184631ae39bb49c1d'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d11_rankCode']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroRankCodeLink','a83b477c13eda000f27e7287eecaa2be404aba44c3c81b907cd4c05cf3017fec');v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 v=r['dependencies']['DiophantineConsistency.Sign33MacroPrefixBPower'];assert v['sha256']=='0abadc08a4ba54e39c9404a8bcffc4b9a742d33333b4c1cefbbf13e69252267f' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroRankComposition.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-rank-composition-prelaunch-frontier-independent/check.py';assert sha(review)=='98af89a053ed1ae044dd2cecee5b8977a21a4f354efb045c6cb787c8b6d3e160'
up=D/'reviews/nine-seed33-jones-rankcode-link-terminal-frontier-independent/check.py';assert sha(up)=='0ad48382332dc1815896d41710172c21dfd87f70ede7e0afa4de966f8add6d81';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
survey=P/'bpower-survey.py';assert sha(survey)=='ffc70e20f1e739d7d596148c4857f8ada5c2c8078d3c04eeb3477ae601789268';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':29827,'stages':1,'guard_slots':150,'overlay_links':1078,'scope':'local d11 rankCode in symbolic d10 entries only; no output equality'},indent=2,sort_keys=True))
