#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-saturated-gap';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(p.read_bytes());ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(b,'big')
beta,K,lo,mf=(ports[n] for n in ('beta','K0','MC','MF'));hi=mf-beta;B=beta.bit_length();assert B==94517 and beta==(1<<B)-1 and 0<lo<beta< mf<2*beta and lo%4==2 and hi%8==4 and lo.bit_count()+hi.bit_count()==B and lo+hi>beta and beta%10==1 and lo%10==8 and mf%10==1 and K%11==0
# Independent repeated block construction and population/carry formulas at actual h=1,2.
for h in (1,2):
 t=B*h;q=1<<t;b=q-1;J=b//beta;assert beta*J==b;A=lo*J;Z=hi*J;g0=q*(Z-1)+A+1
 assert A%4==2 and Z%8==4 and A+Z>b and A.bit_count()+Z.bit_count()==t and g0.bit_count()==t+2 and A+q*(b+Z)-g0==q*q-1
 u,r=divmod(g0,b);assert 2<=u<=b and 1<=r<u and (q-u)>0 and u-r>0
# Exhaustive independent toy masks, then all positive admissible G within each selected mask.
for width in (3,4,5,6):
 q=1<<width;b=q-1
 for A in range(2,b,4):
  for Z in range(4,b,8):
   if A.bit_count()+Z.bit_count()!=width or A+Z<=b:continue
   g0=q*(Z-1)+A+1;assert g0.bit_count()==width+2
   for G in range(4*q-1,q*q-q):
    R=G*(q*q-1)+A+q*(b+Z)
    if G<g0:assert R.bit_count()<=3*width+1
    if R.bit_count()>=3*width+2:
     d=G-g0;assert d>=0 and not (d&g0) and R.bit_count()==3*width+2
     u,r=divmod(G,b);assert 2<=u<=b and 1<=r<u and u-r==q-G%q
# Conditional t divisible by 20: actual port residues imply q10=6, J10=5,
# odd R gives R10=5, hence 2^(R−t)=-1 mod 11.
assert pow(2,20,11)==1 and pow(2,5,11)==10
for t in (20,40,60,100):
 assert pow(2,t,10)==6 and pow(2,t,11)==1
 for G in (1,3,5,7,9):assert ((pow(2,t,10)**2-1)*G+5*(8+pow(2,t,10)))%10==5
# Same-gap repair identity Nt0−Nt = d0*(M+1)−h*(q−1).
for q in range(4,35):
 for F0 in range(2,min(q,8)):
  for d in range(F0):
   F=F0-d;C0=1;C=C0+q*d
   for M in range(1,5):
    for h in range(4):
     assert (M*C0+q-F0)-(M*C+q-F)+(d*M+h)*(q-1)==-d*(M+1)+h*(q-1)
for f in ('current14-carrier64-pell-floor-independent','current14-carrier64-scalar-repair-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text()) and json.loads(r.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'conditional old positive gap at same q,R and odd s; restricted transport congruence remains open, conditional 11-divisor branch; no reverse equivalence/new Lean'},indent=2))
