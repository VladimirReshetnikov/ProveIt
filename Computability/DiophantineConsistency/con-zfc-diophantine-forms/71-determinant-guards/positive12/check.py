#!/usr/bin/env python3
"""Exact algebra, degree, graph, and coefficient checks for the P12 companion."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import gzip,json,random
from build import build
ROOT=Path(__file__).resolve().parent

def require(value,msg):
 if not value: raise ValueError(msg)

def polynomial_ring(n):
 class P(dict):
  def __init__(self,d=0):
   if isinstance(d,int):d={(0,)*n:d}
   super().__init__((k,v) for k,v in d.items() if v)
  def __add__(a,b):
   b=P(b);d=dict(a)
   for k,v in b.items():d[k]=d.get(k,0)+v
   return P(d)
  __radd__=__add__
  def __neg__(a):return P({k:-v for k,v in a.items()})
  def __sub__(a,b):return a+-P(b)
  def __rsub__(a,b):return P(b)+-a
  def __mul__(a,b):
   b=P(b);d={}
   for k,v in a.items():
    for l,w in b.items():
     z=tuple(x+y for x,y in zip(k,l));d[z]=d.get(z,0)+v*w
   return P(d)
  __rmul__=__mul__
  def __pow__(a,k):
   r=P(1)
   for _ in range(k):r=r*a
   return r
  def leading(a,w):
   degree=max(sum(x*y for x,y in zip(k,w)) for k in a)
   return degree,P({k:v for k,v in a.items() if sum(x*y for x,y in zip(k,w))==degree})
 return P,[P({tuple(int(j==k) for k in range(n)):1}) for j in range(n)]

# Exact norm identity, including cancellation at the highest degrees.
P,(A,i,c,B,n)=polynomial_ring(5)
delta=A*A-1;I=i*c*c;D=1+delta*I*I;Q=delta*delta*I*I;d=Q-1
V=D*B-c;t=A*I+n;U=d*((V+t)**2+D)-Q*V*V+1;L=2*d*(V+t)
N=U*U-L*L*D
h=t*t-D
alternative=d*d*h*((t+2*V)**2-D)+2*d*(t*t+D+2*V*t)*(1-V*V)+(1-V*V)**2
require(N==alternative,'norm cancellation identity')
ndeg,head=N.leading([2,1,2,4,1])
require(ndeg==82 and head==4*A**12*i**10*c**20*B**2,'exact norm leader')
require(len(N)==455,'norm term count')

# Prefix identities over independent weighted cut registers q,R and K0.
P,(q,F,alpha,X,Y,r,eta,zeta,gamma,K0,R)=polynomial_ring(11)
k=eta+zeta;c=k*Y+eta;a=X*Y+Y;H=4*a+3;delta=a*a+H
ell=X*k*Y*Y;M0=q**3*(q-1);W=(q-1)*k+1;Bt=(q*K0+X)*(q-F-alpha)-q*F
Z=M0*(ell+k+r)+(q-1)*Y-q**3*W*Bt
A0=Z*Z-M0*M0*(ell*(ell+k)+1)
T0=Z-M0*ell
require(A0==2*M0*ell*T0+T0*T0-M0*M0*ell*k-M0*M0,'first carrier cancellation')
weights=[1]*9+[0,4]
deg0,head0=A0.leading(weights)
require(deg0==15 and head0==-2*q**8*k*k*X*Y*Y*Bt,'first carrier leader')
S=4*q*Y;M=q*S;v=k-R-1;Dstar=M*(X+a*c)+H*(M*gamma-v+S*X)
A1=Dstar*Dstar-M*M*(1+delta*c*c)
deg1,head1=A1.leading(weights)
require(deg1==13 and head1==32*q*q*k*X*X*Y**4*(4*q*q*Y*gamma+R),'main carrier leader')
# The i^10 factor is kept outside this prefix ring.
R4=q**3*(q-F)
full_top=head0*(32*q*q*k*X*X*Y**4*(4*q*q*Y*gamma+R4))*(4*k**20*X**12*Y**32*R4**2)
selected=(18,2,1,16,39,0,23,0,1,0,0)
require(full_top.get(selected)==1024,'nonzero full-polynomial degree coefficient')

# Source graph reproducibility/liveness and counts.
packet=json.loads((ROOT/'adaptive_centered12.json').read_text());rebuilt=build()
require(packet==rebuilt,'literal graph rebuild')
require(packet['operations']==102,'operation count')
seen=set(packet['witnesses']+packet['fixed_numerals'])
for name,op,a,b in packet['source']:
 require(op in ['+','-','*'],'bad operation')
 require(all(isinstance(x,int) or x in seen for x in (a,b)),'forward or undefined register')
 require(name not in seen,'duplicate register');seen.add(name)
needed={packet['output']}
for name,op,a,b in reversed(packet['source']):
 if name in needed:needed.update((a,b))
require(all(row[0] in needed for row in packet['source']),'dead gate')
require(set(packet['witnesses']+packet['fixed_numerals'])<=needed,'dead input')

# Independent scalar formula transcription: finite diagnostics, not identity proofs.
def scalar(v):
 j,F,alpha,i,T,X,Y,r,eta,zeta,n,gamma=[v[z] for z in packet['witnesses']]
 beta,K0,MC,MF=[v[z] for z in packet['fixed_numerals']]
 J=6*j+1;q=beta*J+1;C=q-F-alpha;k=eta+zeta;c=k*Y+eta;a=Y*(X+1);A=a+2;H=4*a+3;delta=A*A-1
 ell=X*k*Y*Y;R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
 M0=q**3*(q-1);W=(q-1)*k+1;Bt=(q*K0+X)*C-q*F
 Z=M0*(ell+k+r)+(q-1)*Y-q**3*W*Bt;A0=Z*Z-M0*M0*(ell*(ell+k)+1)
 S=4*q*Y;M=q*S;Ds=M*(X+a*c)+H*(M*gamma-k+R+1+S*X);A1=Ds*Ds-M*M*(1+delta*c*c)
 I=i*c*c;D=1+delta*I*I;Q=delta*delta*I*I;d=Q-1;V=D*(c*T-R)-c;t=A*I+n
 U=d*((V+t)**2+D)-Q*V*V+1;L=2*d*(V+t);N=U*U-L*L*D
 return (1+A0)*(1+A1)*(1+N)-1
rng=random.Random(20261023)
for _ in range(60):
 v={z:rng.randrange(-3,7) for z in packet['witnesses']+packet['fixed_numerals']};expected=scalar(v)
 def get(x):return x if isinstance(x,int) else v[x]
 for name,op,a,b in packet['source']:
  av,bv=get(a),get(b);v[name]=av+bv if op=='+' else av-bv if op=='-' else av*bv
 require(v[packet['output']]==expected,'scalar diagnostic failed')

# Fixed coefficient bytes are checked against the inherited authentic raw hashes.
auth=json.loads((ROOT/'native/COEFFICIENT_BINDING.original.json').read_text());actual=[]
for entry in auth['materialization']['files']:
 raw=gzip.decompress((ROOT/'native'/entry['file']).read_bytes());digest=sha256(raw).hexdigest()
 require(digest==entry['sha256'],'fixed coefficient hash '+entry['port'])
 actual.append({'port':entry['port'],'sha256':digest,'raw_bytes':len(raw)})
result={'status':'PASS','operations':102,'breakdown':dict(Counter(x[1] for x in packet['source'])),'residual_degrees':[15,13,82],
 'degree':110,'norm_exact_terms':455,'degree_certificate_coefficient':'[j^18 eta^23 X^16 Y^39 i^10 alpha gamma F^2] = 1024*(6*beta)^18 > 0',
 'exact_identities':['first carrier cancellation','weighted first carrier leader','weighted main carrier leader','centered norm cancellation','weighted centered norm leader'],
 'scalar_diagnostics':60,'fixed_coefficients':actual,'proof_boundary':'Finite exact algebra and binding checks; unbounded new reductions in PROOF.md; native and Pell semantic theorems inherited.'}
(ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
