"""Independent finite checks for the two-root/quotient constructions.
These checks validate arithmetic transcription, not Con(ZFC).
"""
import json, random, hashlib, collections, gzip, sys
if not __debug__: raise SystemExit("Run without -O/-OO: all checks must execute.")
from pathlib import Path
HERE=Path(__file__).resolve().parent
PORTS=HERE.parent/'coefficients'/'coefficients'
def payload(f): return gzip.decompress((PORTS/(f+'.gz')).read_bytes())

def add(a,b,p):
 o=[0]*max(len(a),len(b))
 for j,x in enumerate(a):o[j]=(o[j]+x)%p
 for j,x in enumerate(b):o[j]=(o[j]+x)%p
 while len(o)>1 and not o[-1]:o.pop()
 return o

def mul(a,b,p):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]=(o[i+j]+x*y)%p
 while len(o)>1 and not o[-1]:o.pop()
 return o

def evaluate_polynomial(blob,ports,p):
 env={x:[0,3 if x=='t' else 1] for x in blob['witnesses']}
 env.update({x:[v%p] for x,v in ports.items()})
 def get(x):return [x%p] if isinstance(x,int) else env[x]
 for name,op,a,b in blob['source']:
  a,b=get(a),get(b)
  env[name]=mul(a,b,p) if op=='*' else add(a,b if op=='+' else [(-x)%p for x in b],p)
 return env

def norm_product(W,U,S,G,A,p):
 def mm(a,b):
  z=[0]*4
  for i,x in enumerate(a):
   for j,y in enumerate(b):
    z[i^j]=(z[i^j]+x*y*(G if i&j&1 else 1)*(A if i&j&2 else 1))%p
  return z
 acc=[1,0,0,0]
 for sg in (-1,1):
  for st in (-1,1):acc=mm(acc,[W, -sg*U,-st*S,0])
 return acc

def check():
 ports={k:int.from_bytes(payload(f),'little') for k,f in [('beta','beta.bin'),('K0','K.bin'),('MC','MC.bin'),('MF','MF_source.bin')]}
 receipts=[]
 for file in ['thirteen_positive_degree132.json','twelve_positive_degree314.json','twelve_positive_degree258.json','twelve_positive_degree242.json']:
  blob=json.loads((HERE/file).read_text());known=set(blob['witnesses']+blob['fixed_numerals']);needed={blob['output']}
  for name,op,a,b in blob['source']:
   assert name not in known and op in '+-*'
   for x in (a,b):assert isinstance(x,int) or x in known
   known.add(name)
  for name,op,a,b in reversed(blob['source']):
   assert name in needed, 'dead gate'
   needed.update(x for x in (a,b) if isinstance(x,str))
  assert set(blob['witnesses']+blob['fixed_numerals'])<=needed
  assert len(blob['source'])==blob['operations']
  tests=[]
  for p in [1000003,1000033,1000037]:
   env=evaluate_polynomial(blob,ports,p);beta=ports['beta']%p;q=beta;k=2;t=3;X=q;Y=q**3%p;E=X*Y%p;c=k*Y%p;I=c*c%p;R=q**3*(q-1)%p;Nt=-2%p
   Nlead=2**16*1**6*1**9*k**3*q**49*(2*t-k)%p
   assert len(env['N'])-1==68 and env['N'][-1]==Nlead
   if '314' in file:
    expected=Nlead*pow(E,16,p)*pow(I,12,p)*pow(R,4,p)*Nt%p
   elif '258' in file:
    expected=Nlead*pow(E,16,p)*pow(I,8,p)*Nt%p
   elif '242' in file:
    expected=Nlead*pow(c,4,p)*pow(R,4,p)*pow(E,8,p)*pow(I,8,p)*Nt%p
   else:
    expected=-Nlead*pow(E,4,p)*I**2*c**2*Nt%p
   out=env[blob['output']]
   assert len(out)-1==blob['exact_degree']
   assert out[-1]==expected and expected
   tests.append({'prime':p,'degree':len(out)-1,'leading_residue':out[-1]})
  receipts.append({'file':file,'operations':len(blob['source']),'operation_counts':dict(collections.Counter(r[1] for r in blob['source'])),'degree_checks':tests})
 rng=random.Random(257119);norm_cases=0;mod4_cases=0
 for p in [101,1009,1000003]:
  for j in range(100):
   W,U,S,G,A=[rng.randrange(p) for _ in range(5)]
   N=(W*W+U*U*G-S*S*A)**2-4*W*W*U*U*G
   assert norm_product(W,U,S,G,A,p)==[N%p,0,0,0]
   norm_cases+=1
 for j in range(1000):
  W,U,S,G,A,e,d,y,Q,v,b,D=[rng.randrange(-100,101) for _ in range(12)]
  N=(W*W+U*U*G-S*S*A)**2-4*W*W*U*U*G
  B=2*Q*v*b;J=(e-d*y*y)**2-B*B*D
  assert N%4 in (0,1) and J%4 in (0,1)
  mod4_cases+=1
 negpell_cases=0
 for a in range(2,50):
  d=a*a-1
  for y in range(1,500):
   import math
   z=d*y*y-1
   assert math.isqrt(z)**2!=z
   negpell_cases+=1
 quotient_cases=0
 for _ in range(1000):
  M,C,D,v,b,y=[rng.randrange(2,100) for _ in range(6)]
  Q=M*C;d=Q-1;e=Q*(D*v*v+b*b)-1
  Z=C*(D*v*v+b*b-1)+d*y*(2-M*y)
  assert M*Z==e-d*(M*y-1)**2
  quotient_cases+=1
 def pell(a,n):
  x,y=1,0
  for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
  return x,y
 residue_cases=0
 for m in range(2,40):
  for R in range(3,40,4):
   x,y=pell(m,R)
   assert x%m==0 and (y+1)%(m*m)==0
   residue_cases+=1
 # Nontrivial normalized strong + auxiliary quotient fixtures.
 reconstruction_cases=0
 for A0 in range(2,6):
  R=3;_,c=pell(A0,R);f,I=pell(A0,R*c);Delta=A0*A0-1
  assert I%(c*c)==0
  i=I//(c*c);m=Delta*I;Q=m*m
  x,yold=pell(m,R);assert x%m==0;V=x//m
  assert (V+c)%(f*f)==0 and (V+R)%c==0
  T=(V+c+R*f*f)//(c*f)
  assert c*(T*f-1)-R*f*f==V and T>0
  D=f*f;v=c*T;b=c+R*D;d=Q-1
  for M,C in [(Q,1),((Delta*i*c)**2,c*c)]:
   assert M*C==Q and (yold+1)%M==0
   yy=(yold+1)//M
   Z=C*(D*v*v+b*b-1)+d*yy*(2-M*yy)
   assert yy>0 and Z==2*C*v*b*f
   reconstruction_cases+=1
 for pin in json.loads((HERE/'upstream'/'SOURCE_PINS.json').read_text()):
  assert hashlib.sha256((HERE/'upstream'/pin['file']).read_bytes()).hexdigest()==pin['sha256']
 result={'quotient_identity_checks':quotient_cases,'odd_pell_residue_checks':residue_cases,'canonical_auxiliary_reconstruction_checks':reconstruction_cases,'constructions':receipts,'formal_four_factor_norm_checks':norm_cases,'mod4_guard_checks':mod4_cases,'negative_pell_finite_checks':negpell_cases,'coefficient_files':{f:hashlib.sha256(payload(f)).hexdigest() for f in ['beta.bin','K.bin','MC.bin','MF_source.bin']},'limitations':'Finite arithmetic checks do not establish compiler soundness, consistency, or absence of zeros.'}
 (HERE/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':check()
