#!/usr/bin/env python3
import gzip,hashlib,json,math,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/thirteen-variable67-shifted-m-obstruction';src=root/'research/thirteen-variable-independent/polynomial69.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(src)=='3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f';g=json.loads(src.read_bytes());rows=g['source'];by={r[0]:r for r in rows}
for row in (['kY','*','k','Y'],['ell','*','E','kY'],['LB','*','V2','B'],['mLB','-','m','LB'],['h_mLB','*','qm','mLB'],['carrier','-','h_mLB','B'],['y','+','four_carrier',1],['normalized_S','*','hi','Dc2'],['Na','+','aux_product','y2'],['product0','*','N0','N1'],['product1','*','product0','Na'],['product4','*','product1','scaled_Ns'],['polynomial','-','product4','Delta']):assert by[row[0]]==row
new=[]
for row in rows:
 if row[0] in ('LB','mLB'):continue
 new.append(['h_mLB','*','qm','m'] if row[0]=='h_mLB' else row[:])
def live(rs):
 edges={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in edges and x not in seen:seen.add(x);todo.extend(edges[x])
 return seen
assert len(rows)==len(live(rows))==69 and len(new)==len(live(new))==67 and len(g['witnesses'])==13 and 'V2' in live(new)
# This exact graph change makes y=1+4*(b*mu−G), keeping V² live in Na.
assert by['qm']==['qm','*','beta','J'] and by['B']==['B','-','transport','F'] and by['four_carrier']==['four_carrier','*',4,'carrier']
base=(src.parent/g['coefficient_binding']['path']).resolve();ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(base/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(raw,'big')
beta,K,lo,mf=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;hi=mf-beta;assert B==116137 and beta==(1<<B)-1 and K>0 and 0<lo<beta<mf<2*beta
M=lo+q*mf;gap=M+1;R=gap*q*q-1;N=(R-1)//2;assert gap>q*q and R==gap*(q*q-1)+M and R%4==3 and R>3*B and R.bit_count()==348413 and N.bit_count()-1==348411==3*B
exponent=(R-B)%B;assert exponent==40107;wm=pow(2,exponent,beta);mb=(K+wm)%beta
# Independent extended-Euclidean inverse and modular solution for F.
def inverse(a,n):
 oldr,r=n,a%n;oldt,t=0,1
 while r:
  k,rem=divmod(oldr,r);oldr,r=r,rem;oldt,t=t,oldt-k*t
 assert oldr==1
 return oldt%n
inv=inverse(mb+1,beta);assert math.gcd(mb+1,beta)==1 and (mb+1)*inv%beta==1
F=mb*(1-gap)*inv%beta or beta;C=q*(q-F)-gap;alpha=q-F-C
assert 0<F<=beta and C<0 and alpha>0 and beta*(q-F)+alpha==gap and (mb*C-F)%beta==0 and (mb*(1-gap)-(mb+1)*F)%beta==0
fb=F.to_bytes((F.bit_length()+7)//8,'big');assert F.bit_length()==116134 and hashlib.sha256(fb).hexdigest()=='3c062801d0cc3672ac9c9e68569fb5bfe5a9140d35e06c5c7a4db8c67b4687fc'
# m=EY>=2; N odd; v2(Y)=3B gives integral positive s; L chosen in the
# finite norm-one group modulo beta*c² ensures beta*c² divides L.
# The finite auxiliary-unit order modulo S*c*f² makes chi(t)/S congruent
# to chi(R)/S modulo c*f², and t=4*j*order−R is 1 mod 4.
assert N%2==1 and R-B>0 and R>=27 and 3*B<R-1
for f in ('current14-carrier64-toy-full-zero-independent','current14-carrier64-pell-floor-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text())
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','beta_exponent':B,'rank_population':R.bit_count(),'w_exponent_residue':exponent,'F_sha256':hashlib.sha256(fb).hexdigest(),'scope':'2471-port shifted-m 67-gate candidate symbolic positive zero with G<0; original 69-gate same-coordinates obstruction, no unrestricted nonequivalence or Lean/PDF binding'},indent=2))
