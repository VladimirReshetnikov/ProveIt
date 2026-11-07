#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent06-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent06-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='794b89a2cd71e687727028df7c7ae88e3fee21e76ff02d62a364c37d5ce5467c' and sha(A/'outer-terminal-author-record.json')=='8b96cb564eea684c843fc1e477ebb38cc338414d40176ff92642f277a50900ef';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(34719,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1101 and s['runner_sha256']==sha(P/'run.py')=='f7d24112fa4e224ec1fde38c35480e8723f6ac7ffbe0fcdd698801edc0e0baeb';names=['Sign33MacroDependentJcarry','Sign33MacroDependentGprime','Sign33MacroDependentHcarry','Sign33MacroDependentH'];objects=['1a85b3442f137cf8bab206340bcf563670fd79f61ff7abc33a997fbbf2b6db33','1875c457eed36115573a42823b353f51521ca3a17ad62ba1e17e2af6b701b46a','b61e830976be165e3e4dfa1faef87017fc0e4ee9c8539adc1899587756971c15','5b5bf4045f0e4f151681765d3339d847559f324ee47ebc37fc046b120165ce01'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d25_j_carry'],['d32_A_carry','d32_C_carry','d32_D_carry','prefix_Gprime'],['d33_j_carry','d33_Bprime_carry'],['d33_C_carry','prefix_H']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroDependentF','e844c55fd2abd3abb4ca61dedbdc1d194a82a9a6e61cad757ee8b1879fa891c6') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent06.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent06-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='e2e34d1aa76664cd1103737cbc14ed0d8fc7247b7c99ca30d5d1b15e6d685286'
up=D/'reviews/nine-seed33-jones-dependent05-staged-terminal-frontier-independent/check.py';assert sha(up)=='9dc8ae7df36b92e982b81059c814e9670141d724211d6c8f9929c5af6a4b9281';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':34719,'stages':4,'guard_slots':400,'overlay_links':1101,'scope':'local d33–d34 Gprime/H prefix equations and carries only; no output equality'},indent=2,sort_keys=True))
