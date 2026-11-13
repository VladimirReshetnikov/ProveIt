#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-affected-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-affected-cuts-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='0402805f20ab4ba4d22ba3271aac0adff00cd236992f1aba8aa52ff6a49bbd9a' and H(A/'outer-result.json')=='6566e4c2172bb4ae7ae1ed8b886ddeea54f419a6490ae05ac9509c300c9a9cac'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1062 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(74888,0) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='2b9f423151bcdee732eb6a995e2b3ad1a9319e525696a6826950626f0b06df00'
r=s['rows'][0];n='Sign27AffectedCuts';assert r['module']==n and r['source_sha256']=='0764df045edddd2059dbb80699c9ffbdd70f79dce5a299965bbd36f8111d20d4'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==100
assert r['object_sha256']=='f78aed3abe3e52e67a623c6e817685d35103d106cbb057183ed92929faa2115b'==H(O/'lib/DiophantineConsistency'/f'{n}.olean')
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
log=(A/f'{n}-compile.txt').read_text();assert log.count('warning:')==6 and log.count('linter.unusedSimpArgs')==2 and log.count('linter.unusedVariables')==4 and 'sorryAx' not in log and 'error:' not in log
for name in ['MainRoot','Dc2','NormalizedS']:
 for th,ax in [('old_'+name+'_row','[propext]'),('new_'+name+'_row','[propext]'),(name+'_eval','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.Sign27AffectedCuts.{th}' depends on axioms: {ax}" in ' '.join(log.split())
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.Sign27FirstCut'];assert v['sha256']=='9451be9e6d9fb5ecdf40931b8297f66f3fd2cece8d83c36018b2b492e4b77c37' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-affected-cuts-prelaunch-frontier-independent/check.py';assert H(pre)=='cc3ae66672fe0aa0c8fe1e4e50d123dec38492ce51afc1a1dae66d5f5de2fe85'
up=D/'reviews/nine-sharing-sign27-first-cut-retry01-terminal-frontier-independent/check.py';assert H(up)=='d049db4de12602c490af2b6649f1d6c850a5d2982014b2eddd6acc138fdb1549';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':74888,'guards':100,'links':1062,'warnings':6,'scope':'three affected identities only; no assembled zero bridge'},sort_keys=True,indent=2))
