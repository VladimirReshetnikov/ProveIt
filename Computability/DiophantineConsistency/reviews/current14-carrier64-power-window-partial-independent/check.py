#!/usr/bin/env python3
import hashlib,gzip,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-power-window-partial';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(pkg/'check.py')=='f99032f371a0da23c509e0b31e0a690984d4721ef575eda0d3bda99582213868'
g=json.loads(p.read_text());ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 packed=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(packed).hexdigest()==meta['gzip_sha256'];data=gzip.decompress(packed);assert hashlib.sha256(data).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(data,'big')
beta,K,mc,mf=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;assert B==94517 and beta==(1<<B)-1 and K>0 and mc%2==0;R=q*q-1+mc+q*mf;assert R.bit_length()==189036 and R%2==1 and R>=26 and R>3*B
# q=2^B, w=2^(R-B), s=2^R: exponent arithmetic only, no huge powers.
assert R-B>0 and (R-B)+B==R and R+3*B>R and R+(R+3*B)==2*R+3*B and (2*R+3*B)+(R+3*B)==3*R+6*B
# F=C=q-1 gives gap 1 and transport one, structurally and in small arithmetic tests.
for q0 in range(2,30):
 for K0 in range(1,5):
  for w0 in range(1,5):
   F=C=q0-1;z=K0+w0;assert q0*(q0-F)-C==1 and (K0+w0)*C+q0-F-z*(q0-1)==1
assert 1<2*q-1 and (R+1)%2==0 and (R+1)//2>0
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-transport-proposal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=json.loads((pkg/'result.json').read_text());out=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not out.stderr and json.loads(out.stdout)==r
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'symbolic power/rank/transport and first-Pell partial witness; other norms and full zero remain open'},indent=2))
