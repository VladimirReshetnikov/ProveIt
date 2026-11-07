#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-congruence-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-congruence-cuts-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='4efb4fbbfd4750638d0e25ac927611e62869475425860adcef0badfb1db297ca' and H(A/'outer-result.json')=='97755e146d2e46e6860037de33365d8417269c4c79e9e89aafdaa1ab037accd9';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(95243,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1062 and s['runner_sha256']==H(P/'run.py')=='f6ae0b666d86966930d5b74060ca16da1e17765c75c7c92b509af1e3514fe885';r=s['rows'][0];n='Sign26CongruenceCuts';assert r['module']==n and r['source_sha256']=='c239bc0e18ba69ef8683a2e33c18278f80b87a0813caefa29592a30126e934f0'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='8d8280e39e611ccce749fba8b33d7a8b2a78c051b9fa83fb76e053176767e12b'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign26ZeroExtraction','d8eaa2669f1409e398da814af7a9da8560fb82e25d21cb85b0de740146331c47'),('SharingSign27Squares','b7f2a083a1a7a81d57b6fafe67670d8065f43f57396cc2503a38bda0f078bd40')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert log.count('warning:')==2 and log.count('linter.unnecessarySeqFocus')==2 and 'sorryAx' not in log and 'error:' not in log
for th in ['old_Gap_row','old_Tau_row','new_Tau_row','old_Inner_row','new_Inner_row']:assert f"'DiophantineConsistency.Sign26CongruenceCuts.{th}' depends on axioms: [propext]" in log
for th in ['oldGap_zero','first_eval','Tau_eval','Inner_eval']:assert f"'DiophantineConsistency.Sign26CongruenceCuts.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-congruence-cuts-prelaunch-frontier-independent/check.py';assert H(pre)=='2fbbd1197843810cbe7b2d0cb81a81e60330a3b175af0c081b8a98bf5d42d2cf';up=D/'reviews/nine-sharing-sign26-zero-extraction-terminal-frontier-independent/check.py';assert H(up)=='bad783a7578e21edbcffb029ffc809131be27d72a32609ef590a48849640dade';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':95243,'guards':150,'links':1062,'warnings':2,'scope':'gap row/zero, first row and q3-conditional Tau/Inner identities only; no assembled bridge'},sort_keys=True,indent=2))
