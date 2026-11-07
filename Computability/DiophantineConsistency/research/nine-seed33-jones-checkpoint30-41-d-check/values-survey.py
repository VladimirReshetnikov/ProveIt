#!/usr/bin/env python3
"""Authenticate D-node, A-value and checkpoint34 provider routes."""
import hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];B=Path('/tmp/nine-seed33-jones-checkpoint29-41-q-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();obs={}
items=[('dependent04-staged','48eb2457d081e0ff4a2cf94c84a016603d28f9f8bfea606ff252519d23561a81','0591a9e298284e4892bf9e442c63a739024cb15501f22db8821c3ff176a95635','dee52712e01f428376cdbec3d31f4feb8c428b055bd4b5642eeab7ea74fecc54','Sign33MacroDependentD'),('checkpoints27-45-staged','8526c67e2e6c730898f8f3da8e5262b4cbdf9343af43901ef46cc60306829251','2d33d03b58de071f6c0a2b28afe041d708e07a1c1e850632cabe3e13fce92a66','e3bc783ede8685720c679ec3f7712f5a1f26bbda1b615ada4963815db1ec9ef0','Sign33MacroCheckpoint34to41'),('checkpoint24-27-a','8f57f0ee28ce62d6804bb7a1b1d12a77356219e083da4cb9ca0e1d5e048e216f','8d524a4ea8e64118dc49758df0eb14ba59217f3942b352cdd214870efbc82d92','e278b62b0c3b07c1b4a9d10e423bda04603a657a1552d04cc3b2ebdc097f5541','Sign33MacroAValue')]
for group,statehash,checker,result,n in items:
 audit=D/f'reviews/nine-seed33-jones-{group}-terminal-frontier-independent';assert H(audit/'check.py')==checker and H(audit/'result.json')==result
 r=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'check.py')],capture_output=True,text=True,timeout=120);assert r.returncode==0 and json.loads(r.stdout)['status']=='PASS_TERMINAL_AUDIT'
 state=D/f'research/nine-seed33-jones-{group}-check/attempt01/state.json';assert H(state)==statehash;s=json.loads(state.read_text());assert s['status']=='PASS';row=next(x for x in s['rows'] if x['module']==n);orig=Path(f'/tmp/nine-seed33-jones-{group}-check-20261106/lib/DiophantineConsistency')/(n+'.olean');q=B/'lib/DiophantineConsistency'/(n+'.olean');assert q.is_file() and q.resolve()==orig.resolve() and H(q)==row['object_sha256'];obs[n]={'sha256':row['object_sha256'],'realpath':str(orig.resolve())}
print(json.dumps({'status':'PASS','observed':obs,'scope':'Two audited producer routes; deeper ancestry inherited.'},sort_keys=True))
