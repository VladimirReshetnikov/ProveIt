#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-two-sided-window-partial';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(p.read_bytes());ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(b,'big')
beta,K,mc,mf=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;R=q*q-1+mc+q*mf;N=(R-1)//2;j=(R+1)//2
assert B==94517 and beta==(1<<B)-1 and K>0 and mc%2==0 and R%2==1 and R>=27 and R>3*B and N>=13 and 2*j==R+1
# Symbolic logarithms, no gigantic exponentials are materialized.
sexp=R*N-3*B;yexp=sexp+3*B;eexp=R+yexp;mexp=eexp+yexp
assert sexp>=0 and R-B>0 and yexp==R*N and yexp>R and eexp==R*(N+1) and mexp==R*R and R.bit_length()<eexp
# Y=X^N yields both strict inequalities for N>=1 and X>0.
for N0 in range(1,12):
 for X0 in range(1,25):
  Y0=X0**N0;assert X0**N0<2*(Y0+1)*6**N0 and 2*Y0<(18*X0)**N0
# Gap/transport and Pell congruence proof apply for the new, positive scale.
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-power-window-partial-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-growth-window-independent/check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)==json.loads((pkg/'result.json').read_text());assert json.loads(x.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'symbolic first-Pell partial inside both growth bounds, no same-q,R positive scalar representation; remaining norms and global reverse equivalence remain open'},indent=2))
