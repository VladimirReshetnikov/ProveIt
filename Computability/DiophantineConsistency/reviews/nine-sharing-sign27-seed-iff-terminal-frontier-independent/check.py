#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-seed-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-seed-iff-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='0b3293ea500ef8a189088d04c7cef24743900bb084ae0f626009e77e67155f26' and H(A/'outer-result.json')=='0974b559934765e81f068f832e28a2ea877383011dd822a3f720902c1618dd72';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(71996,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1070 and s['runner_sha256']==H(P/'run.py')=='a10f6965e87b77d375df176c376d32c4df1a67115e83139c72edd759be6e8863';r=s['rows'][0];n='Sign27SeedExistential';assert r['module']==n and r['source_sha256']=='f04c523c353bd9bd37067b1146265f6231b19caacb93a6f4924a257c56f8de2a'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='ea89e68026255ad8866317cb855f8ded0ad88d25236e9f82f1e1d79bd9e97cd0'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.Sign27ReverseBridge'];assert v['sha256']=='f2211f087d41951bd6d8724e72c14e11273b98df7d5292d7ace3dd750a11b029' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign27SeedIff.exists_same_input' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-seed-iff-prelaunch-frontier-independent/check.py';assert H(pre)=='3ae2e474e86f1a38d2d322b719f1aaea52040ea45651446ff81b2ac9b8012320';up=D/'reviews/nine-sharing-sign27-zero-bridge-terminal-frontier-independent/check.py';assert H(up)=='d51c419c3a31336f928536ff392fef4bf86ad7a552c75038f458841a1714224e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':71996,'guards':100,'links':1070,'scope':'same-input existential sign27/sign28 zero equivalence under IΣ₁; no source endpoint'},sort_keys=True,indent=2))
