#!/usr/bin/env python3
import collections,gzip,hashlib,json,math,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-free-qminusf-zero';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(source)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';old=json.loads(source.read_bytes());new=json.loads((pkg/'graph.json').read_bytes());before=old['source'];after=new['source'];assert sum(r[0]=='qF' for r in before)==1 and next(r for r in before if r[0]=='qF')==['qF','-','q','F'] and [r[0] for r in before if 'F' in r[2:]]==['qF']
assert after==[[r[0],r[1]]+['u' if v=='qF' else v for v in r[2:]] for r in before if r[0]!='qF'] and new['witnesses']==['u' if x=='F' else x for x in old['witnesses']] and new['fixed_numerals']==old['fixed_numerals'] and new['output']==old['output'] and len(after)==64 and collections.Counter(r[1] for r in after)=={'*':37,'+':16,'-':11}
deps={n:(a,b) for n,_,a,b in after};seen=set();stack=[new['output']]
while stack:
 x=stack.pop()
 if x in seen:continue
 seen.add(x)
 if x in deps:stack.extend(deps[x])
assert all(x in seen for x in list(deps)+new['witnesses']+new['fixed_numerals'])
ports={}
for name,m in old['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(raw,'big')
beta,K,lo,mf=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;hi=mf-beta;assert B==94517 and beta==(1<<B)-1 and K>0 and 0<lo<beta<mf<2*beta and lo%4==2 and hi%8==4 and lo.bit_count()+hi.bit_count()==B
G0=q*(hi-1)+lo+1;G=G0+q**3;R=G*(q*q-1)+lo+q*mf;N=(R-1)//2
assert (G0>>B)&1 and G>=q**3>q*q-q-1 and R==q**5+(G0-q)*q*q+q*q-1 and R.bit_length()==472586 and R>=2*B and R%4==3 and R.bit_count()==3*B+2 and N.bit_count()==3*B+1 and N%2==1 and 3*B<R-1
e=(R-B)%B;assert e==27269;M=(K+pow(2,e,beta))%beta
# Independent extended Euclid, including modular congruence, range, and hash.
def inverse(a,n):
 old_r,r=n,a%n;old_t,t=0,1
 while r:
  k,rem=divmod(old_r,r);old_r,r=r,rem;old_t,t=t,old_t-k*t
 assert old_r==1
 return old_t%n
inv=inverse(M+1,beta);assert math.gcd(M+1,beta)==1 and ((M+1)*inv)%beta==1
u0=((M*G+1)*inv)%beta;low=G//q+1;high=(G-1)//beta;u=u0+max(0,(low-u0+beta-1)//beta)*beta;alpha=G-beta*u;C=u-alpha
assert low<=u<=high and u>q and alpha>0 and C>0 and beta*u+alpha==G and (M*C+u-1)%beta==0 and (M+1)*u%beta==(M*G+1)%beta
ub=u.to_bytes((u.bit_length()+7)//8,'big');assert u.bit_length()==189035 and hashlib.sha256(ub).hexdigest()=='7a8968d57505f15ddbf5f18390aea150274df09c959fc36396b274df70b8c959'
# u>q => M*C+u−1>0, so z is positive integral; old F=q−u is negative.
# General non-circular binomial/Pell/Chebyshev construction reviewed separately.
for f in ('current14-carrier64-current-full-zero-independent','current14-carrier64-toy-full-zero-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text()) and json.loads(r.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','B':B,'rank_bit_length':R.bit_length(),'w_exponent_residue':e,'u_bit_length':u.bit_length(),'u_sha256':hashlib.sha256(ub).hexdigest(),'scope':'distinct free-u candidate has symbolic positive zero at current payload integers, with no old same-q,R positive gap; no maintained zero or existential nonequivalence'},indent=2))
