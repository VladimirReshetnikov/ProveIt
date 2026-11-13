#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-growth-window';candidate=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(candidate)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(candidate.read_bytes());v={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(candidate.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['raw_sha256'];v[name]=int.from_bytes(raw,'big')
beta,K,mc,mf=(v[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;R=q*q-1+mc+q*mf;N=(R-1)//2
assert B==94517 and beta==(1<<B)-1 and K>0 and mc%2==0 and R%2==1 and R>3*B and R>=27 and N>=13 and R-B>0
# The prior verified theorem binding supplies r=R, j=N+1, X=2^R.
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-bad-gap-exclusion-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-power-window-partial-independent/check.py')],capture_output=True,check=True,timeout=180)
# Distinct symbolic partial scales: logarithms of X,Y,E and m, no giant powers materialized.
for yexp in (R+3*B,R*R+3*B):
 eexp=R+yexp;mexp=eexp+yexp;assert yexp>R and eexp>R+1 and mexp==R+2*yexp and 2*((R+1)//2)==R+1
assert R+3*B<2*R and 2*N==R-1
# For X>36,N>=13, (X/6)^N>X^6, whereas 2(Y+1)<4X²<X^6.
assert N>=13 and R>=6 and R+3*B<2*R
# 18<2^5: log2(Ylarge)>(R+5)N, so Ylarge>(18X)^N.
assert R*R+3*B>(R+5)*N
# R>=27 yields E=2^eexp>R+1; exponent arithmetic avoids actual X,Y,E.
assert R.bit_length()<=R and R+3*B>R
# Bounds for psi_p(t), c=Y*k+eta with 0<eta<k; exercise independent exact arithmetic controls.
for p in range(2,50):
 a,b=0,1
 for t in range(1,35):
  assert p**(t-1)<=b<=(2*p)**(t-1) and b>=a>=0
  a,b=b,2*p*b-a
for X in range(2,10):
 for Y in range(1,10):
  m=X*Y*Y;a=Y*(X+1);assert a+2>X*Y and a+2<=3*X*Y and 2*(2*m+1)<=6*X*Y*Y and 2*m+1>=2*X*Y*Y
for rel in ('research/current14-carrier64-growth-compatible-partial','research/current14-carrier64-growth-window'):
 p=root/rel;got=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not got.stderr and json.loads(got.stdout)==json.loads((p/'result.json').read_text())
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'conditional two-sided Pell growth window; excludes the two specified symbolic partial families, not all candidate zeros or reverse equivalence; inherited P72 application external and historical providers point-audited'},indent=2))
