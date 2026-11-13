#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-vars-bd-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-vars-bd-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='3eb2c38bfcc67248e13d2295f7c4bfc37269cf831ce6a4accb90b47e00598d78' and H(A/'outer-terminal-author-record.json')=='b6e3de6e566739ef055828037fac3dd6f58d8f906d0534a5cc31533e99065a23';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(32042,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1167 and s['runner_sha256']==H(P/'run.py')=='48f565f253f5ed61099d6334dbc9bf9964741a7c4b4eed29489bdb7e0f06ffa0';r=s['rows'][0];n='Sign33MacroVarsBd';assert r['module']==n and r['source_sha256']=='c76081ad1c9be62db7a41a3ee47dfe7d65f7f6a0ba87f7f31a9a14db0fefbe6c'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='5134925336ba3fcc50d8ae49922e49f048e347dce85fc9079428ff812904ade8'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.Sign33MacroTerminalOutput'];assert v['sha256']=='2f65b1af4a8a5ee5786093ca0b0ea9c47fe2a247926b461c9eddca0611823324' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
assert "'DiophantineConsistency.Sign33MacroVarsBd.d41_Bd_eq_dvsr' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-vars-bd-prelaunch-frontier-independent/check.py';assert H(pre)=='c3f87ea33e43c81952eaf4a9e08d2aca21febcee250ff9a7155bb7185fd42f5f';up=D/'reviews/nine-seed33-jones-terminal-cut-terminal-frontier-independent/check.py';assert H(up)=='61b076f28933bd5d8409b9d119d31066b22e0705c75be7b0b0258bdb144bd669';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':32042,'guards':100,'links':1167,'scope':'Bd=dvsr with d11 symbolic rank only; no full output semantics'},sort_keys=True,indent=2))
