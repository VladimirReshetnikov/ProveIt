#!/usr/bin/env python3
"""Authenticate checkpoint value providers and their routes into the d18-path overlay."""
import hashlib,json,os,sys,subprocess
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];B=Path('/tmp/nine-seed33-jones-prefix-path18-45-staged-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();obs={}
items=[('live18-staged','a0e202c47a4150d11099175971293d7d28c55dda2d380cfc2a7142c6e6f57e13','3e8a840b8e3b9450e1b3b700e809444fea30795b62f75bbca53fbbd1daf685c0','54af31278c3c143b22ae99ab5e2a3a70e0934fd891deb60cda8527ce875cdfc5',['Sign33MacroLive18Group01','Sign33MacroLive18Group02','Sign33MacroLive18Group03']),('prefix-group03-staged','f1769a73743919a3ff52d3637a514592fdbd5d5222669bc17c404ecee33a29d0','ab4237754322f7aa5c7c769ce0068235e656272fc30a2f7e7910ab2559de8c22','7a5f8787056d592aac8507aa66807fe3919af3b570326a483077997258741da2',['Sign33MacroPrefixGsmall','Sign33MacroPrefixGlarge']),('prefix-group05','f1248d358bf47604cc73a226a6e045379a36cd2c13bcca7ac8bb96d0ffcbb12d','7a444e4e5047b43e23ca34177478b97bcf8a0ba41fe2e7c8bfa1e8467e6805c3','9eff473b56dec3c40078a04d0d7cdecb0fefdd09d85019aa691535b3ab91c364',['Sign33MacroPrefixQNCarry']),('prefix-group04-staged','6ea3f558560d46525b13296b76e6f084cd627eaedd9392beb1e928514363fb0b','2bf2589e50859a05a8d4f59bf2645da6d4d78c5dfc5b8f7fa0b7240f099a2f7d','a6a8ce3e368474e50c97ac7b375911a1ba333d122ad07fb5722dd39177e50503',['Sign33MacroPrefixInputsB'])]
for group,statehash,checker,result,names in items:
 audit=D/f'reviews/nine-seed33-jones-{group}-terminal-frontier-independent';assert H(audit/'check.py')==checker and H(audit/'result.json')==result
 run=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'check.py')],capture_output=True,text=True,timeout=120);assert run.returncode==0 and json.loads(run.stdout)['status']=='PASS_TERMINAL_AUDIT'
 state=D/f'research/nine-seed33-jones-{group}-check/attempt01/state.json';assert H(state)==statehash;s=json.loads(state.read_text());assert s['status']=='PASS'
 for n in names:
  row=next(x for x in s['rows'] if x['module']==n);orig=Path(f'/tmp/nine-seed33-jones-{group}-check-20261106/lib/DiophantineConsistency')/(n+'.olean');q=B/'lib/DiophantineConsistency'/(n+'.olean');assert H(orig)==row['object_sha256']
  if n=='Sign33MacroPrefixInputsB':
   assert not os.path.lexists(q);dep=row['dependencies']['DiophantineConsistency.Sign33MacroPrefixGlarge'];g=B/'lib/DiophantineConsistency/Sign33MacroPrefixGlarge.olean';assert g.is_file() and str(g.resolve())==dep['realpath'] and H(g)==dep['sha256']
   for root in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):assert not os.path.lexists(root/'DiophantineConsistency'/(n+'.olean'))
  else:assert q.is_file() and q.resolve()==orig.resolve() and H(q)==row['object_sha256']
  obs[n]={'sha256':row['object_sha256'],'realpath':str(orig.resolve())}
print(json.dumps({'status':'PASS','observed':obs,'scope':'Seven audited selected producer routes and shared Glarge dependency; deeper ancestry inherited.'},sort_keys=True))
