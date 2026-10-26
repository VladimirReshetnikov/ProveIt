#!/usr/bin/env python3
"""Producer-independent exact sparse algebra and DAG audit: standard library only.
No producer import, external command, networking, or unbounded proof search.
"""
import copy,gzip,hashlib,itertools,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
VARS=['j','C','z','h','r','v','w','T','c','n','p1','p2']
TAG='integer12_degree512'
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
FRONT=[('J','1+6*j'),('qm','J*beta'),('q','1+qm'),('W','4+12*w'),('X','W*q'),('Y','v'),('F','C*(K0+W)-qm*z'),('R','(q*q-q*F-C)*(q*q-1)+J*(MC+MF*q)'),('E','X*Y'),('a','Y+E'),('H','3+4*a'),('Delta','H+a*a'),('ell','E*Y'),('k','1+R+ell*h'),('eta','c-Y*k'),('L','ell*k'),('I','c*c*(1+2*r)'),('Ds','I*I*Delta'),('Fs','Ds+1'),('Q','Ds*Delta'),('V','Fs*(T*c-R)-c'),('q3','q*q*q'),('M','2*q3'),('U','H*M'),('Klo','2*X*X-3*X*c-2'),('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**6'),('G','4*budget-4*p1*p1-4*p2*p2-3')]
END=[('Dt','1+L*L+L*k'),('U2','U*U'),('Zc','U*n+2*U*L+M*Klo+H*Y-H*q3'),('delta','Q-1'),('Cy','V*V*Q-1'),('DU2','U2*delta'),('s','Zc*Zc*delta'),('aa','Fs*DU2'),('bb','Dt*DU2*9'),('cc','G*DU2*729'),('dd','Cy*U2*81'),('sdplus','dd+s'),('acsum','cc+aa'),('acprod','cc*aa'),('pairs','bb*acsum+acprod'),('m','sdplus-bb-acsum'),('m2','m*m'),('sd','dd*s'),('hh','m2+4*sd-4*pairs'),('triple','bb*acprod'),('n0','hh*hh+16*sd*m2-64*triple*sdplus'),('P','n0*n0-64*sd*(m*hh-16*triple)**2')]
FORMS=FRONT+END

def validate(g):
 sy={v:Poly.var(v) for v in set(VARS+PORTS+[n for n,f in FORMS])};ns=g['nodes'];cuts={};covered=set()
 need(g['variables']==VARS and g['variable_count']==12,'variables')
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
 for n,f in FORMS:
  i=g['named_registers'][n]
  need(rec(i,{})==eval(f,{'__builtins__':{}},sy),'formula '+n);cuts[i]=sy[n]
 seen=set()
 def walk(i):
  if i in seen:return
  seen.add(i)
  if ns[i][0] in ['add','sub','mul']:walk(ns[i][1]);walk(ns[i][2])
 walk(g['output']);need(g['output']==g['named_registers']['P'],'output');need(seen==covered==set(range(len(ns))),'liveness/coverage')
 for op,names in [('variable',VARS),('coefficient',PORTS)]:need({r[1] for r in ns if r[0]==op}==set(names),'live '+op)
 counts=dict(Counter(r[0] for r in ns if r[0] in ['add','sub','mul']));need(counts=={'add':25,'mul':82,'sub':25}==g['operation_counts'] and g['operations']==132,'count')
 need(g['exact_degree']==512,'declared degree');need(g['coefficient_binding']=='inherited_round20/inherited/coefficients/BINDING.json' and g['fixed_numerals']==PORTS,'six-port binding')
 return counts

def h4(s,a,b,c,d):
 # Independently written pair norm, with no named producer schedule.
 e=s+d-a-b-c
 h=e*e+4*s*d-4*(a*b+a*c+b*c)
 return (h*h+16*e*e*s*d-64*a*b*c*(s+d))**2-64*s*d*(e*h-16*a*b*c)**2

def algebra():
 z,x,y,v,w=[Poly.var(k) for k in ['z','x','y','v','w']]
 product=Poly.co(1)
 for eps in itertools.product([-1,1],repeat=4):product=product*(z-eps[0]*x-eps[1]*y-eps[2]*v-eps[3]*w)
 need(product==h4(z*z,x*x,y*y,v*v,w*w),'all sixteen formal factors')
 s,a,b,c,d=[Poly.var(k) for k in ['s','a','b','c','d']];norm=h4(s,a,b,c,d)
 need(all(sum(e for v,e in mon)==8 for mon in norm.t),'complete homogeneity')
 deg,top=norm.top(dict(s=48,a=42,b=48,c=46,d=64));need(deg==512 and top==d**8,'complete weighted norm top')
 # The substitution delta times each of the five homogeneous arguments
 # is exactly multiplication by delta^8, including a rational fourth input.
 D=Poly.var('delta');need(h4(D*s,D*a,D*b,D*c,d)==sum((Poly({mon:coef})*D**(8-dict(mon).get('d',0)) for mon,coef in norm.t.items()),Poly.co(0)),'denominator clearing every coefficient')
 # Entire signed-kernel carrier and auxiliary identities.
 Z,U,L,k,Q,V,tau,t=map(Poly.var,['Z','U','L','k','Q','V','tau','t'])
 Dt=1+L*(L+k)
 need((Z+U*k)**2+4*U*(L*Z-U)==(Z+U*(2*L+k))**2-4*U*U*Dt,'carrier square identity')
 yy=t-V
 need(V*V-(Q-1)*yy*(2*V+yy)-1==Q*V*V-(Q-1)*t*t-1,'auxiliary restore identity')
 rho,f,g,n,nn=map(Poly.var,['rho','f','g','n','nn'])
 nold=n-k-f-tau-9*t-27*g
 need((f+3*tau+9*t+27*g)+nold-n+k==2*tau,'new to old carrier map')
 nnew=nn+k+f+tau+9*t+27*g
 need(2*tau-k+nnew-nn==f+3*tau+9*t+27*g,'old to new carrier map')
 # Authentic complete leading form, not a sampled line.
 beta,j,C,z0,w0,v0,r0,c0=map(Poly.var,['beta','j','C','z','w','v','r','c'])
 q0=6*beta*j;a0=12*q0*w0*v0;F0=12*w0*C-q0*z0;R0=-q0**3*F0
 U0=8*q0**3*a0;Q0=4*a0**4*r0*r0*c0**4;V0=-4*a0*a0*r0*r0*c0**4*R0
 dd0=81*U0*U0*Q0*V0*V0
 need(dd0==2**12*3**4*q0**6*a0**10*r0**6*c0**12*R0**2,'entire leading form dd0')
 leading=dd0**8
 target=tuple(sorted(dict(j=192,w=80,v=80,r=48,c=96,z=16,beta=192).items()))
 need(leading.t.get(target)==2**448*3**304,'authentic coefficient')
 need(all(sum(e for v,e in mon if v!='beta')==512 for mon in leading.t),'entire output leading degree')
 digest=hashlib.sha256(json.dumps(norm.canonical(),separators=(',',':')).encode()).hexdigest()
 return dict(norm_terms=len(norm.t),norm_coefficient_sha256=digest,factorization_terms=len(product.t),homogeneous_norm_degree=8,weighted_norm_degree=512,leading_form='(81 U0^2 Q0 V0^2)^8',attained_coefficient='2^448 3^304 beta^192',attained_monomial=dict(j=192,w=80,v=80,r=48,c=96,z=16),whole_denominator_clearing=True,restore_maps=True)

def degree_bounds():
 sy={v:Poly.var(v) for v in set(VARS+PORTS+[n for n,f in FORMS])}
 weights={v:1 for v in VARS};weights.update({v:0 for v in PORTS})
 for n,f in FORMS:
  if n=='sdplus':break
  pp=eval(f,{'__builtins__':{}},sy)
  weights[n]=pp.top(weights)[0]
 expected={'R':5,'a':3,'Delta':6,'I':3,'Fs':12,'Q':18,'V':17,'U':6,'G':16,'Dt':18,'Zc':15,'delta':18,'Cy':52,'s':48,'aa':42,'bb':48,'cc':46,'dd':64}
 need(all(weights[k]==v for k,v in expected.items()),'independently propagated front degree bounds')
 return expected

def mod3():
 # Exhaust all independent input residues needed by the unconditional
 # Delta/Fs/Dt/Q/delta/Cy congruences. Integer multiplication reduces mod3.
 count=0
 for j,w,Y,k,I,V in itertools.product(range(3),repeat=6):
  beta=1;J=6*j+1;q=beta*J+1;W=12*w+4;X=q*W;a=(X+1)*Y;H=4*a+3;Delta=a*a+H
  Fs=1+Delta*I*I;Q=Delta*Delta*I*I;ell=X*Y*Y;Dt=1+ell*(ell+1)*k*k;delta=Q-1;Cy=Q*V*V-1
  need(tuple(x%3 for x in [J,q,W,X,a,H,Delta,Fs,Q,Dt,delta,Cy])==(1,2,1,2,0,0,0,1,0,1,2,2),'mod3 front')
  count+=1
 return count

def authenticate():
 pins=json.loads((ROOT/'INHERITED_PINS.json').read_text())
 for p,h in pins.items():need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'inherited pin '+p)
 base=ROOT/'inherited_round20/inherited/coefficients';bind=json.loads((base/'BINDING.json').read_text());need(set(bind['payloads'])==set(PORTS),'whole tuple');rawbytes=0
 for p in PORTS:
  e=bind['payloads'][p];raw=gzip.decompress((base/e['file']).read_bytes());v=int.from_bytes(raw,'little');rawbytes+=len(raw)
  need(hashlib.sha256(raw).hexdigest()==e['raw_sha256'] and v.bit_length()==e['bits'] and len(raw)==e['raw_bytes'],'coefficient '+p)
  if p=='beta':need(v==2**1064921-1 and v%3==1,'actual beta and residue')
  if p=='cone_A':need(v==2**1113,'cone A')
  if p=='cone_B':need(v==2**666104,'cone B')
 return dict(pinned_files=len(pins),six_coefficient_raw_bytes=rawbytes)

if __name__=='__main__':
 auth=authenticate();g=json.loads((ROOT/(TAG+'.json')).read_text());counts=validate(g);alg=algebra();bounds=degree_bounds();residues=mod3();mutations=0
 for i,r in enumerate(g['nodes']):
  if r[0] not in ['add','sub','mul']:continue
  bad=copy.deepcopy(g);bad['nodes'][i][0]='sub' if r[0]=='add' else 'add'
  try:validate(bad)
  except ValueError:mutations+=1
  else:raise ValueError('accepted gate corruption '+str(i))
 out=dict(status='PASS',optimized=not __debug__,standard_library_only=True,inherited=auth,variables=12,exact_degree=512,operations=132,operation_counts=counts,all_live_gate_mutations_rejected=mutations,universal_algebra=alg,front_degree_bounds=bounds,mod3_exhaustive_residue_fixtures=residues,sha256=hashlib.sha256((ROOT/(TAG+'.json')).read_bytes()).hexdigest(),boundary='Finite exact algebra and coefficient closure; unbounded root separation/descent and inherited ordinary native/refutation calibration are stated separately in PROOF.md.')
 (ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
