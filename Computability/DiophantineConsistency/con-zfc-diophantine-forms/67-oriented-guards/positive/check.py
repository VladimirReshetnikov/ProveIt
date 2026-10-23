#!/usr/bin/env python3
"""Standard-library replay. Finite checks do not prove the imported compiler."""
import gzip,hashlib,json,random,math
from pathlib import Path
from collections import Counter
R=Path(__file__).resolve().parent

def require(p,m):
 if not p:raise ValueError(m)
def load(n):return json.loads((R/n).read_text())
def digest(x):return hashlib.sha256(x).hexdigest()

# Small exact multivariate polynomial ring for universal identities.
class Poly:
 def __init__(self,a=0):self.d=a if isinstance(a,dict) else ({():a} if a else {})
 def __add__(self,b):
  b=P(b);d=self.d.copy()
  for k,v in b.d.items():d[k]=d.get(k,0)+v
  return Poly({k:v for k,v in d.items() if v})
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
 def __sub__(self,b):return self+-P(b)
 def __rsub__(self,b):return P(b)+-self
 def __mul__(self,b):
  b=P(b);d={}
  for k,v in self.d.items():
   for l,w in b.d.items():
    m=tuple(sorted(k+l));d[m]=d.get(m,0)+v*w
  return Poly({k:v for k,v in d.items() if v})
 __rmul__=__mul__
 def __pow__(self,n):
  z=Poly(1)
  for _ in range(n):z=z*self
  return z

def P(a):return a if isinstance(a,Poly) else Poly(a)
def sym(n):return Poly({(n,):1})
def zero(a,m):require(not a.d,m)
q,l,r,Y,k=map(sym,['q','ell','r','Y','k'])
zero((q**3*(l+r)+Y)**2-q**6*(l*(l+k)+1)-(q**6*(r*r+l*(2*r-k)-1)+2*q**3*(l+r)*Y+Y*Y),'first identity')
U,a,c,H,Z=map(sym,['U','a','c','H','Z'])
zero((U*a*c+Z)**2-U**2*((a*a+H)*c*c+1)-(2*U*a*c*Z+Z*Z-U*U*(H*c*c+1)),'main identity')
V,u,Q=map(sym,['V','u','Q'])
zero((V+u)**2-Q*u*(2*V+u)-1-(Q*V*V-(Q-1)*(V+u)**2-1),'auxiliary identity')

pins=load('SOURCE_PINS.json')
for row in pins['sources']:require(digest((R/row['local_path']).read_bytes())==row['sha256'],'source pin '+row['local_path'])
bind=load('coefficients/COEFFICIENT_BINDING.json');ports={}
for row in bind['materialization']['files']:
 rawgz=(R/'coefficients'/row['file']).read_bytes();raw=gzip.decompress(rawgz)
 require(digest(rawgz)==row['gzip_sha256'],'gzip coefficient digest')
 require(digest(raw)==row['sha256'],'raw coefficient digest')
 require(len(raw)==row['raw_bytes'],'coefficient length')
 val=int.from_bytes(raw,'little');require(val.bit_length()==row['bits'],'coefficient bit length');ports[row['port']]=val
require(ports['beta']==2**590069-1,'base binding')
ports['K0']=ports.pop('K');ports['MF']=ports.pop('MF_source')

def run(c,env):
 e=env.copy()
 for name,op,x,y in c['source']:
  a=e[x] if isinstance(x,str) else x;b=e[y] if isinstance(y,str) else y
  e[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return [e[r] for r in c['residuals']],e[c['output']]
def live(c,outputs):
 need=set(outputs)
 for name,op,a,b in reversed(c['source']):
  if name in need:need.update((a,b))
 return [x for x in c['source'] if x[0] in need],need
primary=load('fourteen_positive_degree30.json');cert=load('fourteen_positive_degree30_certificate.json')
for C in [primary,cert]:
 rows,need=live(C,[C['output']]);require(rows==C['source'],'dead gate')
 require(set(C['witnesses']+C['fixed_numerals'])<=need,'missing input')
 require(len(rows)==C['operations'],'count');require(dict(Counter(r[1] for r in rows))==C['operation_counts'],'operation types')
 require(len(C['witnesses'])==14,'variables')
require(primary['operations']==87,'primary cost');require(len(live(primary,primary['residuals'])[0])==78,'system cost')
system=load('fourteen_positive_system.json')
require(system['source']==live(primary,primary['residuals'])[0] and system['outputs']==primary['residuals'] and system['operations']==78,'system artifact')

def formula(e):
 J,F,al,z,f,i,T,w,Y,r,eta,zeta,u,ga=[e[n] for n in primary['witnesses']]
 q=e['beta']*J+1;C=q-F-al;X=w*q;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;D=a*a+H;l=E*k*Y
 R0=((q-1)*(q-F)+al)*(q*q-1)+(e['MC']+q*e['MF'])*J
 U=4*q*Y;v=k-R0-1;ds=U*(X+a*c)+H*(U*ga-v);Q=D*(f*f-1);V=f*f*(c*T-R0)-c
 res=[(q**3*(l+r)+Y)**2-q**6*(l*(l+k)+1),ds*ds-U*U*(D*c*c+1),(i*c*c)**2-Q,(V+u)**2-Q*u*(2*V+u)-1,(e['K0']+w)*C+q-F-z*(q-1)-1]
 return res,sum(t*t for t in res)
rng=random.Random(340087)
for j in range(100):
 e={n:rng.randint(-5,9) for n in primary['witnesses']};e.update({n:rng.randint(1,31) for n in ports})
 require(run(primary,e)==formula(e)==run(cert,e),'independent evaluation')

# Adaptive-modulus examples cover powers of3 and arbitrary extra scale primes.
for q in range(2,80):
 for ss in range(1,12):
  Y=ss*q**3;X=(ss+1)*q;H=4*Y*(X+1)+3;U=4*q*Y
  require(U>=4*q**4 and (4*X*Y*Y)%U==0 and math.gcd(U,H)<=3,'adaptive modulus check')

# Univariate specialization with actual fixed ports, coefficients reduced mod p.
def padd(a,b,p,sgn=1):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]=(c[i]+x)%p
 for i,x in enumerate(b):c[i]=(c[i]+sgn*x)%p
 while c and not c[-1]:c.pop()
 return c
def pmul(a,b,p):
 c=[0]*max(0,len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
 while c and not c[-1]:c.pop()
 return c
receipts=[]
for p in [101,1009,1000003]:
 env={n:[0,1] for n in primary['witnesses']};env.update({n:[v%p] for n,v in ports.items()})
 env['r']=[0,3]
 def polys(c):
  e=env.copy()
  for n,op,x,y in c['source']:
   a=e[x] if isinstance(x,str) else [x%p];b=e[y] if isinstance(y,str) else [y%p]
   e[n]=pmul(a,b,p) if op=='*' else padd(a,b,p,1 if op=='+' else -1)
  return [e[t] for t in c['residuals']],e[c['output']]
 a,b=polys(primary),polys(cert);require(a==b,'actual-port polynomial identity')
 degs=[len(t)-1 for t in a[0]];require(degs==[12,14,10,15,2],'specialized residual degrees')
 require(len(a[1])-1==30,'degree 30 witness');require(a[1][-1]==4*pow(ports['beta'],10,p)*pow(ports['beta']-1,2,p)%p,'leading coefficient')
 receipts.append({'prime':p,'residual_degrees':degs,'degree':30,'leading_coefficient':a[1][-1]})
# Universal upper degrees are certified by the cancellation circuit.
deg={n:1 for n in primary['witnesses']};deg.update({n:0 for n in ports})
for n,op,x,y in cert['source']:
 a=deg[x] if isinstance(x,str) else 0;b=deg[y] if isinstance(y,str) else 0
 deg[n]=a+b if op=='*' else max(a,b)
require([deg[n] for n in cert['residuals']]==[12,14,10,15,2],'universal upper bound')
require(deg[cert['output']]==30,'universal output upper bound')
report={'checks':'passed','universal_identities':3,'random_literal_formula_cases':100,'source_pins':len(pins['sources']),'coefficient_payloads':4,'adaptive_modulus_cases':858,'positive_unknowns':14,'degree':30,'operations':87,'system_operations':78,'specializations':receipts,'status':'Finite arithmetic audits, not an end-to-end kernel proof.'}
(R/'CHECK_RECEIPT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
