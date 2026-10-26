#!/usr/bin/env python3
"""Independent exact sparse algebra, literal DAG and complete coefficient audit.
Standard library only; no builder/circuit import, network, or zero search.
"""
import copy,gzip,hashlib,itertools,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
VARS=['j','C','z','h','r','v','w','T','c','n','y','p2','p3']
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
 f += [('eta','c-Y*k'),('L','ell*k' if short else 'E*Y*k'),('I','c*c*(4+8*r)'),('Ds','I*I*Delta'),('Fs','1+Ds'),('Q','Ds*Delta'),('delta','Q-1'),('b','T*c-R'),('dy','y*delta'),('t','dy+c'),('tt','t*t'),('Lb','b*b*Fs'),('Ares','Lb+tt-(Q*y)*dy-1'),('Hres','Ares*Ares-(2*Lb)*(2*tt)'),('q3','q*q*q'),('M','2*q3'),('U','H*M'),('Klo','2*X*X-3*X*c-2'),('Z','U*n+U*L+M*Klo+H*Y-H*q3' if short else 'U*n+M*Klo+H*Y-H*q3'),('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**6' if short else 'Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q*q*q3*q3'),('pos2','1+p2*p2+p3*p3+p3'),('G','budget-pos2'),('Dt','1+L*L+L*k'),('U2','U*U'),('ga','G*U2'),('db','Dt*U2'),('N','(Z*Z-db-ga)**2-4*db*ga'),('P','(N+1)*(Hres+1)-1')]
 return f

def validate(g,short):
 fs=forms(short);sy={v:Poly.var(v) for v in set(VARS+PORTS+[n for n,f in fs])};ns=g['nodes'];cuts={};covered=set()
 need(g['variables']==VARS and g['variable_count']==13,'variables')
 need(set(g['named_registers'])=={n for n,f in fs},'all named registers exactly bound')
 for i,row in enumerate(ns):
  need(row[0] in ['variable','coefficient','integer','add','sub','mul'],'node tag')
  if row[0] in ['add','sub','mul']:need(len(row)==3 and all(type(k)==int and 0<=k<i for k in row[1:]),'topology')
  elif row[0]=='integer':need(type(row[1])==int,'integer leaf')
  else:need(len(row)==2 and row[1] in (VARS if row[0]=='variable' else PORTS),'leaf binding')
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
 counts=dict(Counter(r[0] for r in ns if r[0] in ['add','sub','mul']));want={'add':27,'mul':66,'sub':21} if short else {'add':26,'mul':65,'sub':21}
 need(counts==want==g['operation_counts'] and g['operations']==sum(want.values()),'count')
 need(g['exact_degree']==(118 if short else 120),'declared degree');need(g['coefficient_binding']=='inherited_round22/inherited_round20/inherited/coefficients/BINDING.json' and g['fixed_numerals']==PORTS,'whole six-port binding')
 return counts

def algebra():
 f,Fs,b,c,y,Q=map(Poly.var,['f','Fs','b','c','y','Q'])
 delta=Q-1;t=c+delta*y;Lb=Fs*b*b
 A=Lb+t*t-Q*delta*y*y-1
 Aclear=Fs*b*b+c*c-1-delta*y*(y-2*c)
 need(A==Aclear,'complete resultant cancellation38to22')
 V=f*b-c;Ea=V*V-delta*y*(2*V+y)
 need(Ea-1==A-2*b*t*f+b*b*(f*f-Fs),'complete auxiliary linearization')
 H=A*A-4*Lb*t*t
 need(H==(A-2*b*t*f)*(A+2*b*t*f)+4*b*b*t*t*(f*f-Fs),'complete signed resultant identity')
 N=Poly.var('N');need(N*H+N+H==(N+1)*(H+1)-1,'expanded unit finalizer')
 x,p,t,G,D,U,L,k,Z,n=map(Poly.var,['x','p','t','G','D','U','L','k','Z','n'])
 norm=(x*x-G-D)**2-4*G*D;product=Poly.co(1)
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
 return dict(complete_resultant_cancellation=True,complete_auxiliary_linearization=True,complete_signed_resultant_identity=True,expanded_unit_finalizer=True,signed_four_factor_norm=True,rational_root_extraction=True,whole_carrier_identity=True,both_root_maps=True)

def degree_proof(short):
 Z,U,L,k,G,D=map(Poly.var,['Z','U','L','k','G','D'])
 if short:
  zc=Z+U*L;dt=1+L*(L+k);cut=zc*zc-U*U*dt
  need(cut==Z*Z+2*U*L*Z-U*U*(1+L*k),'complete center cancellation')
  N=(cut-U*U*G)**2-4*U**4*G*dt
  deg,top=N.top(dict(Z=7,U=6,L=9,k=5,G=16))
  need(deg==58 and top==-4*U**4*L*L*G,'entire norm top118')
 else:
  N=(Z*Z-U*U*(G+D))**2-4*U**4*G*D
  deg,top=N.top(dict(Z=7,U=6,G=18,D=18))
  need(deg==60 and top==U**4*(G-D)**2,'entire norm top120')
 b,c,y,Fs,Q=map(Poly.var,['b','c','y','Fs','Q'])
 delta=Q-1;t=c+delta*y;Lb=Fs*b*b;A=Lb+t*t-Q*delta*y*y-1;H=A*A-4*Lb*t*t
 weights=dict(b=5,c=1,y=1,Fs=12,Q=18)
 ad,at=A.top(weights);hd,ht=H.top(weights)
 need(ad==22 and at==Fs*b*b,'whole cancelled resultant-linear degree')
 need(hd==60 and ht==-4*Fs*b*b*Q*Q*y*y,'whole resultant top60')
 beta,j,C,z,h,w,v,r=map(Poly.var,['beta','j','C','z','h','w','v','r'])
 q0=6*beta*j;X0=12*q0*w;a0=X0*v;ell0=X0*v*v
 F0=12*w*C-q0*z;R0=-q0**3*F0;U0=8*q0**3*a0;I0=8*r*c*c
 D0=a0*a0*I0*I0;Q0=a0**4*I0*I0
 htop=-4*D0*R0**2*Q0**2*y*y
 need(htop==-2**20*a0**10*r**6*c**12*R0**2*y*y,'whole resultant inherited-front leading form')
 if short:
  k0=R0+h*ell0;T0=Poly.var('cone_A')**2*v*v*F0*F0+4*q0*q0*v**4+q0**6
  nt=4*U0**4*ell0**2*k0**4*T0
  target=dict(j=58,w=16,v=18,z=6,r=6,c=12,y=2,beta=58);coef=-2**124*3**74
 else:
  nt=U0**4*R0**4*(q0**8+ell0**2)**2
  target=dict(j=66,w=14,v=14,z=6,r=6,c=12,y=2,beta=66);coef=-2**126*3**80
 outtop=nt*htop
 need(outtop.t.get(tuple(sorted(target.items())))==coef,'authentic attained coefficient')
 need(all(sum(e for v,e in m if v not in PORTS)==(118 if short else 120) for m in outtop.t),'entire output homogeneous top')
 leading={'names':['N','Hres','P'],'polynomials':[nt.canonical(),htop.canonical(),outtop.canonical()]}
 (ROOT/('LEADING118.json' if short else 'LEADING120.json')).write_text(json.dumps(leading,indent=2)+'\n')
 return dict(exact_degree=118 if short else 120,norm_degree=deg,resultant_linear_degree=ad,resultant_degree=hd,leading_terms=len(outtop.t),monomial={v:e for v,e in target.items() if v!='beta'},coefficient=('-2^124 3^74 beta^58' if short else '-2^126 3^80 beta^66'),complete_leading_form_checked=True)

def finite_controls():
 # Exhaustive finite residue facts, not the unbounded signed proof.
 units=0
 for a,h in itertools.product(range(4),repeat=2):
  need((a*a)%4!=2 and (h*h)%4!=2,'mod4 square excludes minus-two');units+=1
 rows=0
 for c in range(-12,13):
  if c==0:continue
  for delta in [abs(c)+1,144*c**4-1]:
   for y in range(-12,13):need(c+delta*y!=0,'guarded t diagnostic');rows+=1
 for R in range(1,30):
  for c in [-R-1,R+1]:
   for T in range(-20,21):need(c*T-R!=0,'guarded b diagnostic');rows+=1
 # An explicit degenerate false-positive resultant if guard omitted.
 f=0;Fs=2;b=0;c=1;Q=3;y=0;t=c+(Q-1)*y;A=Fs*b*b+c*c-1-(Q-1)*y*(y-2*c)
 need(A*A-Fs*(2*b*t)**2==0 and b*t==0,'exceptional branch control')
 # Fs=2 is not a rational square; this demonstrates the missing-root danger.
 need(1*1<2<2*2,'non-square exceptional control')
 return dict(mod4_square_cases=units,nonvanishing_diagnostic_rows=rows,unguarded_resultant_exception_exhibited=True)

def authenticate():
 pins=json.loads((ROOT/'INHERITED_PINS.json').read_text())
 need(pins and all(p.startswith('inherited_round22/') for p in pins),'pin scope')
 actual={p.relative_to(ROOT).as_posix() for p in (ROOT/'inherited_round22').rglob('*') if p.is_file()}
 need(actual==set(pins),'complete inherited closure coverage')
 for p,h in pins.items():need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'source pin '+p)
 base=ROOT/'inherited_round22/inherited_round20/inherited/coefficients';bind=json.loads((base/'BINDING.json').read_text());need(set(bind['payloads'])==set(PORTS),'whole tuple');rawbytes=0
 for p in PORTS:
  e=bind['payloads'][p];raw=gzip.decompress((base/e['file']).read_bytes());v=int.from_bytes(raw,'little');rawbytes+=len(raw)
  need(hashlib.sha256(raw).hexdigest()==e['raw_sha256'] and v.bit_length()==e['bits'] and len(raw)==e['raw_bytes'],'coefficient '+p)
  if p=='beta':need(v==2**1064921-1 and v%3==1,'actual beta')
  if p=='cone_A':need(v==2**1113,'cone A')
  if p=='cone_B':need(v==2**666104,'cone B')
 return dict(pinned_files=len(pins),six_coefficient_raw_bytes=rawbytes)

def literal_occurrence(g):
 # A nonzero formal partial at one fixed modular point proves actual occurrence.
 prime=1000003;base=ROOT/'inherited_round22/inherited_round20/inherited/coefficients'
 bind=json.loads((base/'BINDING.json').read_text());co={}
 for k,v in bind['payloads'].items():co[k]=int.from_bytes(gzip.decompress((base/v['file']).read_bytes()),'little')%prime
 point={v:2*i+3 for i,v in enumerate(VARS)};values=[];derivatives=[]
 for row in g['nodes']:
  op=row[0];d=[0]*len(VARS)
  if op=='integer':value=row[1]%prime
  elif op=='coefficient':value=co[row[1]]
  elif op=='variable':value=point[row[1]];d[VARS.index(row[1])]=1
  else:
   a,b=row[1:];va,vb=values[a],values[b];da,db=derivatives[a],derivatives[b]
   if op=='add':value=(va+vb)%prime;d=[(x+y)%prime for x,y in zip(da,db)]
   elif op=='sub':value=(va-vb)%prime;d=[(x-y)%prime for x,y in zip(da,db)]
   else:value=va*vb%prime;d=[(x*vb+va*y)%prime for x,y in zip(da,db)]
  values.append(value);derivatives.append(d)
 gradient=derivatives[g['output']];need(all(gradient),'every variable occurs on actual fixed slice')
 return {'prime':prime,'point':point,'gradient':dict(zip(VARS,gradient)),'all_variables_genuinely_occur':True}

if __name__=='__main__':
 auth=authenticate();alg=algebra();controls=finite_controls();rows=[]
 for short,tag in [(True,'integer13_degree118'),(False,'integer13_degree120')]:
  g=json.loads((ROOT/(tag+'.json')).read_text());counts=validate(g,short);degree=degree_proof(short);occurrence=literal_occurrence(g);mutations=0
  for i,r in enumerate(g['nodes']):
   if r[0] not in ['add','sub','mul']:continue
   for op in set(['add','sub','mul'])-{r[0]}:
    bad=copy.deepcopy(g);bad['nodes'][i][0]=op
    try:validate(bad,short)
    except (ValueError,KeyError,IndexError):mutations+=1
    else:raise ValueError('accepted gate corruption '+str(i)+' '+op)
  rows.append(dict(name=tag,variables=13,operations=sum(counts.values()),operation_counts=counts,all_live_gate_mutations_rejected=mutations,degree_proof=degree,occurrence=occurrence,sha256=hashlib.sha256((ROOT/(tag+'.json')).read_bytes()).hexdigest()))
 out=dict(status='PASS',optimized=not __debug__,standard_library_only=True,inherited=auth,universal_algebra=alg,diagnostics=controls,endpoints=rows,boundary='Finite literal, algebra and coefficient checks; unbounded guarded extraction and inherited ordinary signed/native/refutation theorem are separately stated in PROOF.md.')
 (ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
