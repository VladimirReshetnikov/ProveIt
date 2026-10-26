#!/usr/bin/env python3
"""Independent exact sparse algebra, literal DAG and complete coefficient audit.
Standard library only; no builder/circuit import, network, or zero search.
"""
import copy,gzip,hashlib,itertools,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
VARS=['j','C','z','h','r','v','w','T','c','n','f','y','p2','p3']
def need(ok,msg):
 if not ok:raise ValueError(msg)
class Poly:
 def __init__(self,terms=None):self.t={m:c for m,c in (terms or {}).items() if c}
 @staticmethod
 def co(x):return x if isinstance(x,Poly) else Poly({():x})
 @staticmethod
 def var(v):return Poly({((v,1),):1})
 def __add__(self,b):
  b=self.co(b);t=dict(self.t)
  for m,c in b.t.items():t[m]=t.get(m,0)+c
  return Poly(t)
 __radd__=__add__
 def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
 def __sub__(self,b):return self+-self.co(b)
 def __rsub__(self,b):return self.co(b)+-self
 def __mul__(self,b):
  b=self.co(b);t={}
  for m,c in self.t.items():
   for n,d in b.t.items():
    ex=dict(m)
    for v,e in n:ex[v]=ex.get(v,0)+e
    k=tuple(sorted((v,e) for v,e in ex.items() if e));t[k]=t.get(k,0)+c*d
  return Poly(t)
 __rmul__=__mul__
 def __pow__(self,k):
  need(type(k)==int and k>=0,'natural exponent');out=self.co(1);b=self
  while k:
   if k&1:out=out*b
   b=b*b;k//=2
  return out
 def __eq__(self,b):return self.t==self.co(b).t
 def subs(self,e):
  out=self.co(0)
  for mon,c in self.t.items():
   term=self.co(c)
   for v,k in mon:term=term*e.get(v,self.var(v))**k
   out=out+term
  return out
 def top(self,w):
  deg=max(sum(w[v]*k for v,k in m) for m in self.t)
  return deg,Poly({m:c for m,c in self.t.items() if sum(w[v]*k for v,k in m)==deg})
 def canonical(self):return [[list(m),c] for m,c in sorted(self.t.items())]
def forms(short):
 f=[('J','1+6*j'),('qm','J*beta'),('q','1+qm'),('W','4+12*w'),('X','W*q'),('Y','v'),('F','C*(K0+W)-qm*z'),('R','(q*q-q*F-C)*(q*q-1)+J*(MC+MF*q)'),('E','X*Y'),('a','Y+E'),('H','3+4*a'),('Delta','H+a*a')]
 if short:f += [('ell','Y*E'),('k','1+R+ell*h')]
 else:f += [('k','1+R+E*h')]
 f += [('eta','c-Y*k'),('L','ell*k' if short else 'E*Y*k'),('I','c*c*(4+8*r)'),('Q','(f*f-1)*Delta'),('V','(T*c-R)*f-c'),('q3','q*q*q'),('M','2*q3'),('U','H*M'),('Klo','2*X*X-3*X*c-2'),('Z','U*n+U*L+M*Klo+H*Y-H*q3' if short else 'U*n+M*Klo+H*Y-H*q3'),('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**6' if short else 'Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q*q*q3*q3'),('pos2','1+p2*p2+p3*p3+p3'),('G','budget-pos2'),('strong','f*f-I*I*Delta'),('uu','V*V+2*V*y+y*y'),('auxiliary','(1-Q)*uu+Q*V*V'),('Dt','1+L*L+L*k'),('U2','U*U'),('ga','G*U2'),('db','Dt*U2'),('N','(Z*Z-db-ga)**2-4*db*ga'),('P','strong*(N+1)*auxiliary-1')]
 return f

def validate(g,short):
 fs=forms(short);sy={v:Poly.var(v) for v in set(VARS+PORTS+[n for n,f in fs])};ns=g['nodes'];cuts={};covered=set()
 need(g['variables']==VARS and g['variable_count']==14,'variables')
 for i,row in enumerate(ns):
  need(row[0] in ['variable','coefficient','integer','add','sub','mul'],'node tag')
  if row[0] in ['add','sub','mul']:need(len(row)==3 and all(type(k)==int and 0<=k<i for k in row[1:]),'topology')
  elif row[0]=='integer':need(type(row[1])==int,'integer leaf')
 def rec(i,memo):
  if i in cuts:return cuts[i]
  if i in memo:return memo[i]
  covered.add(i);r=ns[i]
  if r[0]=='integer':x=Poly.co(r[1])
  elif r[0] in ('variable','coefficient'):x=sy[r[1]]
  else:
   a,b=rec(r[1],memo),rec(r[2],memo);x=a+b if r[0]=='add' else a-b if r[0]=='sub' else a*b
  memo[i]=x;return x
 for n,f in fs:
  i=g['named_registers'][n];need(rec(i,{})==eval(f,{'__builtins__':{}},sy),'formula '+n);cuts[i]=sy[n]
 seen=set()
 def walk(i):
  if i in seen:return
  seen.add(i)
  if ns[i][0] in ['add','sub','mul']:walk(ns[i][1]);walk(ns[i][2])
 walk(g['output']);need(g['output']==g['named_registers']['P'],'output');need(seen==covered==set(range(len(ns))),'liveness/coverage')
 for op,names in [('variable',VARS),('coefficient',PORTS)]:need({r[1] for r in ns if r[0]==op}==set(names),'live '+op)
 counts=dict(Counter(r[0] for r in ns if r[0] in ['add','sub','mul']));want={'add':24,'mul':63,'sub':23} if short else {'add':23,'mul':62,'sub':23}
 need(counts==want==g['operation_counts'] and g['operations']==sum(want.values()),'count')
 need(g['exact_degree']==(85 if short else 87),'declared degree');need(g['coefficient_binding']=='inherited_round20/inherited/coefficients/BINDING.json' and g['fixed_numerals']==PORTS,'whole six-port binding')
 return counts

def algebra():
 x,p,t,G,D,U,L,k,Z,n=map(Poly.var,['x','p','t','G','D','U','L','k','Z','n'])
 norm=(x*x-G-D)**2-4*G*D
 product=Poly.co(1)
 for e1,e2 in itertools.product([-1,1],repeat=2):product=product*(x-e1*p-e2*t)
 need(product==norm.subs({'G':p*p,'D':t*t}),'all four signed factors')
 need((x*x+G-D)**2-4*x*x*G==norm,'square extraction p')
 need((x*x+D-G)**2-4*x*x*D==norm,'square extraction tau')
 Dt=1+L*(L+k)
 need((Z+U*k)**2+4*U*(L*Z-U)==(Z+U*(2*L+k))**2-4*U*U*Dt,'carrier identity')
 for s in [0,1]:
  nold=n+s*L-(2*L+k)-p+t
  need((p+t)+nold-n-s*L+2*L+k==2*t,'restored carrier '+str(s))
  nnew=n-s*L+2*L+k+p-t
  need(2*t+nnew-n+s*L-(2*L+k)==p+t,'inverse carrier '+str(s))
 f0,I0,Delta=map(Poly.var,['f0','I0','Delta'])
 # On f0^2-Delta I0^2=1, the double also has norm one.
 double=(2*f0*f0-1)**2-Delta*(2*f0*I0)**2-1
 need(double==4*f0*f0*(f0*f0-Delta*I0*I0-1),'doubled strong norm')
 V,Q,y=map(Poly.var,['V','Q','y'])
 need((V+y)**2-Q*((V+y)**2-V*V)==V*V-(Q-1)*y*(2*V+y),'shared auxiliary full identity')
 need(V*V-(Q-1)*y*(2*V+y)-1==Q*V*V-(Q-1)*(V+y)**2-1,'adjacent auxiliary identity')
 return dict(signed_four_factor_norm=True,rational_root_extraction=True,whole_carrier_identity=True,both_root_maps=True,doubled_strong_norm=True,auxiliary_restore=True)

def degree_proof(short):
 Z,U,L,k,G,D=map(Poly.var,['Z','U','L','k','G','D'])
 if short:
  zc=Z+U*L;dt=1+L*(L+k)
  cut=zc*zc-U*U*dt
  need(cut==Z*Z+2*U*L*Z-U*U*(1+L*k),'complete center cancellation')
  N=(cut-U*U*G)**2-4*U**4*G*dt
  deg,top=N.top(dict(Z=7,U=6,L=9,k=5,G=16))
  need(deg==58 and top==-4*U**4*L*L*G,'entire norm top85')
 else:
  N=(Z*Z-U*U*(G+D))**2-4*U**4*G*D
  deg,top=N.top(dict(Z=7,U=6,G=18,D=18))
  need(deg==60 and top==U**4*(G-D)**2,'entire norm top87')
 b,c,f,y,Delta,r=map(Poly.var,['b','c','f','y','Delta','r'])
 aux=(f*b-c)**2-(Delta*(f*f-1)-1)*y*(2*(f*b-c)+y)
 ad,at=aux.top(dict(b=5,c=1,f=1,y=1,Delta=6))
 need(ad==15 and at==-2*Delta*f**3*b*y,'entire auxiliary top')
 strong=f*f-Delta*((8*r+4)*c*c)**2
 sd,st=strong.top(dict(f=1,Delta=6,r=1,c=1))
 need(sd==12 and st==-64*Delta*r*r*c**4,'entire strong top')
 beta,j,C,z,h,w,v=map(Poly.var,['beta','j','C','z','h','w','v'])
 q0=6*beta*j;X0=12*q0*w;a0=X0*v;ell0=X0*v*v
 F0=12*w*C-q0*z;R0=-q0**3*F0;U0=8*q0**3*a0
 if short:
  k0=R0+h*ell0;T0=Poly.var('cone_A')**2*v*v*F0*F0+4*q0*q0*v**4+q0**6
  nt=4*U0**4*ell0**2*k0**4*T0
  target=dict(j=48,w=10,v=12,z=5,r=2,c=4,f=3,y=1,beta=48);coef=-2**89*3**58
 else:
  nt=U0**4*R0**4*(q0**8+ell0**2)**2
  target=dict(j=56,w=8,v=8,z=5,r=2,c=4,f=3,y=1,beta=56);coef=-2**91*3**64
 outtop=nt*(-64*a0*a0*r*r*c**4)*(2*a0*a0*f**3*R0*y)
 need(outtop.t.get(tuple(sorted(target.items())))==coef,'authentic attained coefficient')
 need(all(sum(e for v,e in m if v not in PORTS)==(85 if short else 87) for m in outtop.t),'entire output homogeneous top')
 return dict(exact_degree=85 if short else 87,norm_degree=deg,auxiliary_degree=ad,strong_degree=sd,leading_terms=len(outtop.t),monomial={v:e for v,e in target.items() if v!='beta'},coefficient=('-2^89 3^58 beta^48' if short else '-2^91 3^64 beta^56'),complete_leading_form_checked=True)

def finite_controls():
 # Diagnostics supplement, never replace, the unbounded recurrence proof.
 rows=0
 for B in range(2,15):
  ps=[0,1];cs=[1,B]
  for m in range(2,81):ps.append(2*B*ps[-1]-ps[-2]);cs.append(2*B*cs[-1]-cs[-2])
  for m in range(81):need(ps[m]%2==m%2,'Pell ordinate parity')
  for m in range(1,81,2):
   if B%4==2:need(cs[m]%4==2,'odd canonical trace mod4')
  for p in range(1,8):
   c=ps[p]
   for m in range(1,81):
    if ps[m]%(c*c)==0 and ps[m]%2==0:need(cs[m]%c==1%c,'even-strong trace congruence')
  rows+=81
 for f in range(16):
  for a in range(16):need((f*f-16*a)%16!=15,'strong unit excludes minus one')
 return dict(pell_recurrence_diagnostic_rows=rows,mod16_strong_unit_cases=256)

def authenticate():
 pins=json.loads((ROOT/'INHERITED_PINS.json').read_text())
 for p,h in pins.items():need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'source pin '+p)
 base=ROOT/'inherited_round20/inherited/coefficients';bind=json.loads((base/'BINDING.json').read_text());need(set(bind['payloads'])==set(PORTS),'whole tuple');rawbytes=0
 for p in PORTS:
  e=bind['payloads'][p];raw=gzip.decompress((base/e['file']).read_bytes());v=int.from_bytes(raw,'little');rawbytes+=len(raw)
  need(hashlib.sha256(raw).hexdigest()==e['raw_sha256'] and v.bit_length()==e['bits'] and len(raw)==e['raw_bytes'],'coefficient '+p)
  if p=='beta':need(v==2**1064921-1 and v%3==1,'actual beta')
  if p=='cone_A':need(v==2**1113,'cone A')
  if p=='cone_B':need(v==2**666104,'cone B')
 return dict(pinned_files=len(pins),six_coefficient_raw_bytes=rawbytes)

if __name__=='__main__':
 auth=authenticate();alg=algebra();controls=finite_controls();rows=[]
 for short,tag in [(True,'integer14_degree85'),(False,'integer14_degree87')]:
  g=json.loads((ROOT/(tag+'.json')).read_text());counts=validate(g,short);degree=degree_proof(short);mutations=0
  for i,r in enumerate(g['nodes']):
   if r[0] not in ['add','sub','mul']:continue
   bad=copy.deepcopy(g);bad['nodes'][i][0]='sub' if r[0]=='add' else 'add'
   try:validate(bad,short)
   except ValueError:mutations+=1
   else:raise ValueError('accepted gate corruption '+str(i))
  rows.append(dict(name=tag,variables=14,operations=sum(counts.values()),operation_counts=counts,all_live_gate_mutations_rejected=mutations,degree_proof=degree,sha256=hashlib.sha256((ROOT/(tag+'.json')).read_bytes()).hexdigest()))
 out=dict(status='PASS',optimized=not __debug__,standard_library_only=True,inherited=auth,universal_algebra=alg,diagnostics=controls,endpoints=rows,boundary='Finite literal, algebra and coefficient checks; unbounded Pell arguments and inherited ordinary native/refutation theorem are separately stated in PROOF.md.')
 (ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
