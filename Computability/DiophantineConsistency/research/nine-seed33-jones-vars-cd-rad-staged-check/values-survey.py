#!/usr/bin/env python3
"""Authenticate terminal node, input and checkpoint providers and their Bd-overlay routes."""
import hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];B=Path('/tmp/nine-seed33-jones-vars-bd-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();obs={}
items=[('dependent08-staged', '3a068e06a3ca8fc3c246a846037280fc84f558244dc456677c097bd9ee8e0c6d', 'f8908d411729a7b1f1bcf121aeb653e43f7902749bf83a8dca7e40e03291f0ce', 'a708d806cc00347ffec0b3f936fbeb762fab9a7860b5ad5acc64303900089ef1', 'Sign33MacroDependentOutput'), ('prefix-path18-45-staged', 'aa759798f6726970f460be1bd46bb99d5c361d428a7cf386b7743671e7c82cdb', '84b526564578d6e72fcb47fea066c1b199f9731ad344b2c251bb904695306513', 'c00a3b2b2ce97dce8c5d1fd4d9d4b942d354c50fac58e0632853dd0214f0c312', 'Sign33MacroPath18to41'), ('prefix-group04-staged', '6ea3f558560d46525b13296b76e6f084cd627eaedd9392beb1e928514363fb0b', '2bf2589e50859a05a8d4f59bf2645da6d4d78c5dfc5b8f7fa0b7240f099a2f7d', 'a6a8ce3e368474e50c97ac7b375911a1ba333d122ad07fb5722dd39177e50503', 'Sign33MacroPrefixInputsB')]
for group,statehash,checker,result,n in items:
 audit=D/f'reviews/nine-seed33-jones-{group}-terminal-frontier-independent';assert H(audit/'check.py')==checker and H(audit/'result.json')==result
 r=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'check.py')],capture_output=True,text=True,timeout=120);assert r.returncode==0 and json.loads(r.stdout)['status']=='PASS_TERMINAL_AUDIT'
 state=D/f'research/nine-seed33-jones-{group}-check/attempt01/state.json';assert H(state)==statehash;s=json.loads(state.read_text());assert s['status']=='PASS';row=next(x for x in s['rows'] if x['module']==n);orig=Path(f'/tmp/nine-seed33-jones-{group}-check-20261106/lib/DiophantineConsistency')/(n+'.olean');q=B/'lib/DiophantineConsistency'/(n+'.olean');assert q.is_file() and q.resolve()==orig.resolve() and H(q)==row['object_sha256'];obs[n]={'sha256':row['object_sha256'],'realpath':str(orig.resolve())}
print(json.dumps({'status':'PASS','observed':obs,'scope':'Three audited producer routes; deeper ancestry inherited.'},sort_keys=True))
