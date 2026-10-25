#!/usr/bin/env python3
"""Independent formula binding, cancellation cuts, fixed degree and mutations.
Does not import the builder/circuit or execute inherited source.
"""
import copy,gzip,hashlib,itertools,json
from pathlib import Path
from collections import Counter
import sympy as S
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
VARS=['j','C','z','h','r','v','w','T','c','n','y','p1','p2']
TAG='integer13_degree152_ops119'
FRONT=[('J','1+6*j'),('qm','J*beta'),('q','1+qm'),('W','4+12*w'),('X','W*q'),('Y','v'),('F','C*(K0+W)-qm*z'),('R','(q*q-q*F-C)*(q*q-1)+J*(MC+MF*q)'),('E','X*Y'),('a','Y+E'),('H','3+4*a'),('Delta','H+a*a'),('ell','E*Y'),('k','1+R+ell*h'),('eta','c-Y*k'),('L','ell*k'),('I','c*c*(1+2*r)'),('Ds','I*I*Delta'),('Fs','Ds+1'),('Q','Ds*Delta'),('V','Fs*(T*c-R)-c'),('q3','q*q*q'),('M','2*q3'),('U','H*M'),('Klo','2*X*X-3*X*c-2'),('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**6'),('G','4*budget-4*p1*p1-4*p2*p2-3')]
COMMON=[('Dt','1+L*L+L*k'),('U2','U*U'),('ga','G*U2'),('db','4*Dt*U2'),('fc','16*Fs*U2')]
NEW=FRONT+[('uu','(V+y)**2'),('auxiliary','Q*V*V+(1-Q)*uu')]+COMMON+[('Zc','U*n+2*U*L+M*Klo+H*Y-H*q3'),('gc','fc+ga'),('Z2','Zc*Zc'),('gaf','fc*ga'),('inner','(Z2-gc-db)**2-4*gaf-4*db*gc'),('N','inner*inner-64*gaf*db*Z2'),('P','N*auxiliary+auxiliary-1')]
OLD=FRONT+[('Z','U*n+M*Klo+H*(Y-q3)'),('carrier','(Z+U*k)**2+4*U*(L*Z-U)'),('auxiliary','V*V-(Q-1)*y*(2*V+y)')]+COMMON+[('gc','ga+fc'),('inner','(carrier-gc)**2-4*(ga*fc+db*gc)'),('N','inner*inner-64*ga*db*fc*(carrier+db)'),('P','(N+1)*auxiliary-1')]
def need(v,m):
 if not v:raise ValueError(m)
def validate(g,old=False):
 forms=OLD if old else NEW;sy={v:S.Symbol(v) for v in set(VARS+PORTS+[n for n,f in forms])};ns=g['nodes'];cuts={};covered=set()
 need(g['variables']==VARS and g['variable_count']==13,'variables')
 for i,row in enumerate(ns):
  need(row[0] in ['variable','coefficient','integer','add','sub','mul'],'node tag')
  if row[0] in ['add','sub','mul']:need(len(row)==3 and all(type(k)==int and 0<=k<i for k in row[1:]),'topology')
 def rec(i,memo):
  if i in cuts:return cuts[i]
  if i in memo:return memo[i]
  covered.add(i);r=ns[i]
  if r[0]=='integer':x=S.Integer(r[1])
  elif r[0] in ('variable','coefficient'):x=sy[r[1]]
  else:
   a,b=rec(r[1],memo),rec(r[2],memo);x=a+b if r[0]=='add' else a-b if r[0]=='sub' else a*b
  memo[i]=x;return x
 for n,f in forms:
  i=g['named_registers'][n]
  need(S.expand(rec(i,{})-S.sympify(f,locals=sy))==0,'formula '+n);cuts[i]=sy[n]
 seen=set()
 def walk(i):
  if i in seen:return
  seen.add(i)
  if ns[i][0] in ['add','sub','mul']:
   walk(ns[i][1]);walk(ns[i][2])
 walk(g['output']);need(g['output']==g['named_registers']['P'],'output');need(seen==covered==set(range(len(ns))),'liveness/coverage')
 for op,names in [('variable',VARS),('coefficient',PORTS)]:need({r[1] for r in ns if r[0]==op}==set(names),'live '+op)
 counts=dict(Counter(r[0] for r in ns if r[0] in ['add','sub','mul']));expected={'add':26,'mul':76,'sub':24} if old else {'add':24,'mul':71,'sub':24}
 need(counts==expected==g['operation_counts'] and g['operations']==sum(expected.values()),'count')
 need(g['exact_degree']==152,'declared degree')
 if not old:need(g['coefficient_binding']=='inherited/coefficients/BINDING.json' and g['fixed_numerals']==PORTS,'six-port binding')
 return counts

def weighted_top(expr,vs,weights):
 terms=S.Poly(S.expand(expr),*vs).terms();d=max(sum(x*w for x,w in zip(m,weights)) for m,c in terms)
 top=sum(c*S.prod(x**e for x,e in zip(vs,m)) for m,c in terms if sum(x*w for x,w in zip(m,weights))==d)
 return d,S.expand(top)
def universal_and_degree():
 Z,U,L,k,G,Fs=S.symbols('Z U L k G Fs');Dt=1+L*(L+k);b=2*L+k
 ca=lambda z:(z+U*k)**2+4*U*(L*z-U)
 ga=U*U*G;db=4*U*U*Dt;fc=16*U*U*Fs;zc=Z+2*U*L
 cold=ca(Z-U*k)
 ccut=Z*Z+4*U*L*Z-4*U*U*(1+L*k)
 need(S.expand(cold-ccut)==0,'partial shear carrier')
 need(S.expand(zc*zc-db-ccut)==0,'entire degree30 cancellation')
 oldin=(cold-ga-fc)**2-4*(ga*fc+db*(ga+fc))
 newin=(zc*zc-ga-fc-db)**2-4*(ga*fc+db*(ga+fc))
 oldN=oldin**2-64*ga*db*fc*(cold+db)
 newN=newin**2-64*ga*db*fc*zc*zc
 need(S.expand(oldin-newin)==0 and S.expand(oldN-newN)==0,'whole norm after shear')
 ds,top=weighted_top(newin,[Z,U,L,k,G,Fs],[7,6,9,5,16,12]);need(ds==58 and S.expand(top+16*U**4*L*L*G)==0,'complete degree58 inner')
 dn,ntop=weighted_top(newN,[Z,U,L,k,G,Fs],[7,6,9,5,16,12]);need(dn==116 and S.expand(ntop-256*U**8*L**4*G*G)==0,'complete norm degree116')
 vv,yy,qq=S.symbols('V y Q');u2=(vv+yy)**2;ea=u2-qq*(u2-vv*vv)
 need(S.expand(ea-(vv*vv-(qq-1)*yy*(2*vv+yy)))==0,'complete auxiliary cancellation')
 da,atop=weighted_top(ea,[vv,yy,qq],[17,1,18]);need(da==36 and S.expand(atop+2*qq*vv*yy)==0,'auxiliary degree36')
 # Exact eight signed factors, without a nonzero-carrier division.
 x,g,t,f=S.symbols('x g t f');prod=S.prod(x-a*g-2*bb*t-4*c*f for a,bb,c in itertools.product([-1,1],repeat=3))
 norm=((x*x-g*g-4*t*t-16*f*f)**2-4*(4*g*g*t*t+16*g*g*f*f+64*t*t*f*f))**2-4096*g*g*t*t*f*f*x*x
 need(S.expand(prod-norm)==0,'all signed factors')
 sy={v:S.Symbol(v) for v in VARS+PORTS};q=6*sy['beta']*sy['j'];X=12*q*sy['w'];Y=sy['v'];F=12*sy['w']*sy['C']-q*sy['z'];R=-q**3*F;ell=X*Y**2;k0=R+sy['h']*ell;a=X*Y;U0=8*q**3*a
 T0=sy['cone_A']**2*Y**2*F**2+4*q**2*Y**4+q**6
 n0=4096*U0**8*ell**4*k0**8*T0**2
 a0=32*a**6*sy['r']**4*sy['c']**8*R*sy['y'];full=n0*a0
 # Zeroing C,h discards only terms absent from the selected target monomial.
 reduced=S.Poly(S.expand(full.subs({sy['C']:0,sy['h']:0})),*[sy[v] for v in VARS if v not in ['C','h']])
 mon={'j':90,'w':18,'v':22,'z':9,'r':4,'c':8,'y':1};cf=reduced.coeff_monomial(tuple(mon.get(v,0) for v in VARS if v not in ['C','h']))
 need(S.expand(cf-2**167*3**108*sy['beta']**90)==0,'actual fixed coefficient')
 need(sum(mon.values())==152,'total degree')
 return {'whole_polynomial_shear':'n_old=n_new-k','inner_degree':58,'norm_degree':116,'auxiliary_degree':36,'exact_degree':152,'norm_top':'4096 U0^8 ell0^4 k0^8 T0^2','auxiliary_top':'32 a0^6 r^4 c^8 R0 y','actual_coefficient':{'monomial':mon,'coefficient':'2^167 3^108 beta^90'},'negative_zero_shared_squareclass_cases':'Unbounded argument in PROOF.md; exact signed factorization checked.'}

def authenticate():
 pins=json.loads((ROOT/'INHERITED_PINS.json').read_text())
 for p,h in pins.items():need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'inherited pin '+p)
 bind=json.loads((ROOT/'inherited/coefficients/BINDING.json').read_text());rawbytes=0
 need(set(bind['payloads'])==set(PORTS),'complete tuple')
 for p in PORTS:
  e=bind['payloads'][p];raw=gzip.decompress((ROOT/'inherited/coefficients'/e['file']).read_bytes());v=int.from_bytes(raw,'little');rawbytes+=len(raw)
  need(hashlib.sha256(raw).hexdigest()==e['raw_sha256'] and v.bit_length()==e['bits'] and len(raw)==e['raw_bytes'],'coefficient '+p)
  if p=='beta':need(v==2**1064921-1,'beta')
  if p=='cone_A':need(v==2**1113,'cone A')
  if p=='cone_B':need(v==2**666104,'cone B')
 return {'pinned_files':len(pins),'six_coefficient_raw_bytes':rawbytes}
if __name__=='__main__':
 auth=authenticate();g=json.loads((ROOT/(TAG+'.json')).read_text());old=json.loads((ROOT/'inherited/integer13_degree152.json').read_text());oc=validate(old,True);nc=validate(g);degree=universal_and_degree();mutations=0
 for i,r in enumerate(g['nodes']):
  if r[0] not in ['add','sub','mul']:continue
  bad=copy.deepcopy(g);bad['nodes'][i][0]='sub' if r[0]=='add' else 'add'
  try:validate(bad)
  except ValueError:mutations+=1
  else:raise ValueError('accepted gate corruption '+str(i))
 out={'status':'PASS','optimized':not __debug__,'inherited':auth,'parent_operations':sum(oc.values()),'new_operations':sum(nc.values()),'operation_counts':nc,'all_live_gate_mutations_rejected':mutations,'degree_and_universal':degree,'sha256':hashlib.sha256((ROOT/(TAG+'.json')).read_bytes()).hexdigest(),'boundary':'Finite algebra and literal metrics; inherited native/refutation calibration remains ordinary theorem, not a newly rebuilt kernel certificate.'}
 (ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
