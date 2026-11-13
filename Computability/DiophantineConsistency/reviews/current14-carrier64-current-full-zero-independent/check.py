#!/usr/bin/env python3
import gzip,hashlib,json,math,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-current-full-zero';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';graph=root/'research/current14-carrier64-transport-proposal/graph.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(graph)=='f3bc67492c0aa88c9881bf7e2c39e1586e38b3324305b025b010c0912625af43'
g=json.loads(p.read_bytes());ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
beta,K,lo,mf=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;hi=mf-beta;assert B==94517 and beta==(1<<B)-1 and K>0 and 0<lo<beta<mf<2*beta and lo%4==2 and hi%8==4 and lo.bit_count()+hi.bit_count()==B and lo+hi>beta
G=q*(hi-1)+lo+1;R=G*(q*q-1)+lo+q*mf;N=(R-1)//2
assert R==(G+1)*q*q-1 and R.bit_length()==330831 and R>=2*B and R%4==3 and G.bit_count()==B+2 and R.bit_count()==3*B+2 and N.bit_count()==3*B+1 and N%2==1
u,alpha=divmod(G,beta);F0=q-u;C0=u-alpha;assert u==hi and alpha==lo+hi-beta and F0==q-hi and C0==beta-lo and 2<=u<=beta and 1<=alpha<u and 0<F0<q and 0<C0<q
# Compute w mod beta by the Mersenne period without ever materializing w.
e=(R-B)%B;assert e==54265;wm=pow(2,e,beta);M=(K+wm)%beta
# Independent extended Euclid for the exact 94517-bit modular inverse.
def inverse(a,n):
 old_r,r=n,a%n;old_t,t=0,1
 while r:
  k,rem=divmod(old_r,r);old_r,r=r,rem;old_t,t=t,old_t-k*t
 assert old_r==1
 return old_t%n
inv=inverse(M+1,beta);assert ((M+1)*inv)%beta==1 and math.gcd(M+1,beta)==1
d=((F0-M*C0)*inv)%beta;db=d.to_bytes((d.bit_length()+7)//8,'big');assert d.bit_length()==94514 and hashlib.sha256(db).hexdigest()=='57379339931be15b25510d19cbf4b903f5cddd8f2fd9e683372d2e44b0a2487e' and 0<d<F0
F=F0-d;C=C0+q*d;assert 0<F<q and C>0 and q*(q-F)-C==G and (M*C-F)%beta==0 and (M*C0-F0)%beta!=0 and q-F-C==alpha-beta*d<0
# Exponents and integer/positivity consequences of the symbolic binomial Y.
assert N>=13 and 2*N+1==R and N.bit_count()-1==3*B and R-B>=B and 2*N+1>=27
# Y has positive leading and central terms; its central-binomial v2 is 3B,
# all remaining terms are multiples of 2^(R-1); hence s=Y/2^(3B) is odd.
assert 3*B<R-1
# H−T<1/4 and ratio−H<1/4, for T's own interval, are justified in README;
# finite exact-rational controls and general Pell/Chebyshev recurrences reviewed separately.
for f in ('current14-carrier64-pell-floor-independent','current14-carrier64-toy-full-zero-independent','current14-carrier64-saturated-gap-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text()) and json.loads(r.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','B':B,'rank_bit_length':R.bit_length(),'w_exponent_residue':e,'delta_bit_length':d.bit_length(),'delta_sha256':hashlib.sha256(db).hexdigest(),'scope':'symbolic 64-candidate full positive zero at authenticated current port payload integers; no same-q,R,w old scalar repair; maintained equation/existential equivalence/PDF binding not established'},indent=2))
