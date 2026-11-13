#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-gap-representative-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-gap-representative-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='6442f901ccda54040fb5d0c1b4ec883f17755c810f76488358cca0bd8f19372b' and H(A/'outer-result.json')=='6dc4ffc029738db364e3f4ce80b1ae16ea159dde9e95a6e6cd9a96fbb1ad25c1';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(74682,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1060 and s['runner_sha256']==H(P/'run.py')=='c462f09dc30287998a257c55d51d98db08d677e01d8319d9b8f77a3b17afab09';r=s['rows'][0];n='Sign26GapRepresentative';assert r['module']==n and r['source_sha256']=='4dd1a475c13562f8039fa7e1b99f54b0b2a2b08d5c2e5d55e00f3c4649d5c3bf'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='0d73c1b243d9b5271a270304148f86c96022e84fea7db8d3534b6feaeb0507b3'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('DiophantineConsistency.SharingSign26Squares','49bddc37c95ec053d290fc8314dc7cea089f4cce33baec24ee000fc44d573eb3'),('Sign26OrderedRing','d4ace8e8669574bc73d52462787dc7624a630f8d8429f92163de3ab20baf24f9')]:
 v=r['dependencies'][mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign26GapRepresentative.exists_gap' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-gap-representative-prelaunch-frontier-independent/check.py';assert H(pre)=='a787dcb3f25645cc47e15a074d86fec6773ee12eb48a369e8e0b47295d997ca1';up=D/'reviews/nine-sharing-sign26-ordered-ring-retry01-terminal-frontier-independent/check.py';assert H(up)=='07bbdfd68a4e7821dd75b1ce5b1eb04bb62a2cb8750157e253828c03198555fd';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':74682,'guards':150,'links':1060,'scope':'conditional natural gap representative given beta≥1 and embedded Nt equality; no seed/cast discharge'},sort_keys=True,indent=2))
