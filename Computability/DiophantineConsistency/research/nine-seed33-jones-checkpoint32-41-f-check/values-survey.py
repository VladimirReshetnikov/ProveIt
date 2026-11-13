#!/usr/bin/env python3
"""Authenticate F-node and checkpoint34 providers and their E-overlay routes."""
import hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];B=Path('/tmp/nine-seed33-jones-checkpoint31-41-e-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();obs={}
items=[('dependent05-staged','70254e03d48c21f71f1ae4ae31a576d70491c9ff316ab65f9b0285ef35de38c9','9dc8ae7df36b92e982b81059c814e9670141d724211d6c8f9929c5af6a4b9281','963ad41346fb459631758e538085072eaeec63e8a6e75c2e018ef7dcac8640a6','Sign33MacroDependentF'),('checkpoints27-45-staged','8526c67e2e6c730898f8f3da8e5262b4cbdf9343af43901ef46cc60306829251','2d33d03b58de071f6c0a2b28afe041d708e07a1c1e850632cabe3e13fce92a66','e3bc783ede8685720c679ec3f7712f5a1f26bbda1b615ada4963815db1ec9ef0','Sign33MacroCheckpoint34to41')]
for group,statehash,checker,result,n in items:
 audit=D/f'reviews/nine-seed33-jones-{group}-terminal-frontier-independent';assert H(audit/'check.py')==checker and H(audit/'result.json')==result
 r=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'check.py')],capture_output=True,text=True,timeout=120);assert r.returncode==0 and json.loads(r.stdout)['status']=='PASS_TERMINAL_AUDIT'
 state=D/f'research/nine-seed33-jones-{group}-check/attempt01/state.json';assert H(state)==statehash;s=json.loads(state.read_text());assert s['status']=='PASS';row=next(x for x in s['rows'] if x['module']==n);orig=Path(f'/tmp/nine-seed33-jones-{group}-check-20261106/lib/DiophantineConsistency')/(n+'.olean');q=B/'lib/DiophantineConsistency'/(n+'.olean');assert q.is_file() and q.resolve()==orig.resolve() and H(q)==row['object_sha256'];obs[n]={'sha256':row['object_sha256'],'realpath':str(orig.resolve())}
print(json.dumps({'status':'PASS','observed':obs,'scope':'Two audited producer routes; deeper ancestry inherited.'},sort_keys=True))
