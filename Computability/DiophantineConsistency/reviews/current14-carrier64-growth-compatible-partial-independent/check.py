#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-growth-compatible-partial';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(pkg/'check.py')=='0e5030599504989280c9974ad34815ceeef87fc2020ab04d138c156d4fb75aa2'
g=json.loads(p.read_bytes());ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(b,'big')
beta,K,mc,mf=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;R=q*q-1+mc+q*mf;N=(R-1)//2;j=(R+1)//2
assert B==94517 and beta==(1<<B)-1 and K>0 and mc%2==0 and R%2==1 and R>=27 and R>3*B and 2*j==R+1
# Symbolic logarithms: X=wq, Y=sq³, E=XY, m=EY; no exponential materialization.
yexp=R*R+3*B;eexp=R+yexp;mexp=eexp+yexp
assert R-B>0 and (R-B)+B==R and yexp>R*N and eexp==R*R+R+3*B and mexp==2*R*R+R+6*B and R.bit_length()<eexp
# G=1, Nt=1, and no same-q,R old positive scalar are scale-independent.
for q0 in range(2,50):
 for K0 in range(1,5):
  for w0 in range(1,5):
   F=C=q0-1;z=K0+w0;assert q0*(q0-F)-C==1 and (K0+w0)*C+(q0-F)-z*(q0-1)==1 and 2*q0-1>1
# Prior review establishes the symbolic Pell norm/congruence identities for arbitrary E|m.
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-transport-proposal-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-power-window-partial-independent/check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)==json.loads((pkg/'result.json').read_text())
assert yexp>(R+5)*N # 18<2^5: separately violates upper growth condition.
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'first-Pell/transport/rank symbolic partial meets lower growth inequality, but separately fails upper growth inequality; no full-zero or general reverse-map claim'},indent=2))
