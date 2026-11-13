#!/usr/bin/env python3
"""Authenticate M and live18 producers and their routes into the U/Y overlay."""
import hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];B=Path('/tmp/nine-seed33-jones-checkpoint20-27-uy-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();obs={}
items=[('live18-staged','a0e202c47a4150d11099175971293d7d28c55dda2d380cfc2a7142c6e6f57e13','3e8a840b8e3b9450e1b3b700e809444fea30795b62f75bbca53fbbd1daf685c0','54af31278c3c143b22ae99ab5e2a3a70e0934fd891deb60cda8527ce875cdfc5','Sign33MacroLive18Group02'),('dependent02-staged','5e4bb01a6e6e638335fe40d01bbaa8eb10e04fd43156ff8c8c37693186f64a17','c663a5ba9ee0a038349f035833770b9c64db8e7e14a4b43c548a3370720f2141','140f22b09b25082f2a543c45b5bcd5aa0742f2902e6a3fb4bdd34b63a8b0b565','Sign33MacroDependentM')]
for group,statehash,checker,result,n in items:
 audit=D/f'reviews/nine-seed33-jones-{group}-terminal-frontier-independent';assert H(audit/'check.py')==checker and H(audit/'result.json')==result
 r=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'check.py')],capture_output=True,text=True,timeout=120);assert r.returncode==0 and json.loads(r.stdout)['status']=='PASS_TERMINAL_AUDIT'
 state=D/f'research/nine-seed33-jones-{group}-check/attempt01/state.json';assert H(state)==statehash;s=json.loads(state.read_text());assert s['status']=='PASS';row=next(x for x in s['rows'] if x['module']==n);orig=Path(f'/tmp/nine-seed33-jones-{group}-check-20261106/lib/DiophantineConsistency')/(n+'.olean');q=B/'lib/DiophantineConsistency'/(n+'.olean');assert q.is_file() and q.resolve()==orig.resolve() and H(q)==row['object_sha256'];obs[n]={'sha256':row['object_sha256'],'realpath':str(orig.resolve())}
print(json.dumps({'status':'PASS','observed':obs,'scope':'Two audited producer routes; deeper ancestry inherited.'},sort_keys=True))
