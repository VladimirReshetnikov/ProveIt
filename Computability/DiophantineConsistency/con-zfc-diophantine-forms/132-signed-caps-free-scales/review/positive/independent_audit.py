#!/usr/bin/env python3
"""Independent audit: imports no producer/checker or source program.
Canonical free-expression identities, literal graph census, byte bindings,
independent modular polynomials and isolated corruption controls.
"""
from pathlib import Path
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import gzip,json,random
HERE=Path(__file__).resolve().parent
PKG=HERE.parent.parent/'positive'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def digest(p):return sha256(p.read_bytes()).hexdigest()
class Ring:
 def __init__(self):self.nodes=[];self.memo={}
 def intern(self,t):
  if t not in self.memo:self.memo[t]=len(self.nodes);self.nodes.append(t)
  return E(self,self.memo[t])
 def C(self,v):return self.intern(('c',v))
 def S(self,v):return self.intern(('s',v))
 def coerce(self,x):return x if isinstance(x,E) else self.C(x)
 def scalar(self,x):
  t=self.nodes[x.i]
  if t[0]=='c':return t[1],None
  if t[0]=='m':return t[1],self.intern(('m',1,t[2])) if t[1]!=1 else x
  return 1,x
 def add(self,a,b):
  terms=Counter();constant=0
  for x in (a,b):
   t=self.nodes[x.i]
   source=t[2] if t[0]=='a' else ((x.i,1),)
   if t[0]=='a':constant+=t[1]
   for i,k in source:
    c,y=self.scalar(E(self,i))
    if y is None:constant+=k*c
    else:terms[y.i]+=k*c
  terms=tuple(sorted((i,c) for i,c in terms.items() if c))
  if not terms:return self.C(constant)
  if constant==0 and len(terms)==1:
   i,c=terms[0]
   if c==1:return E(self,i)
   return self.mul(self.C(c),E(self,i))
  return self.intern(('a',constant,terms))
 def mul(self,a,b):
  coeff=1;factors=Counter()
  for x in (a,b):
   t=self.nodes[x.i]
   if t[0]=='c':coeff*=t[1]
   elif t[0]=='m':coeff*=t[1];factors.update(dict(t[2]))
   else:factors[x.i]+=1
  if coeff==0:return self.C(0)
  if not factors:return self.C(coeff)
  if coeff==1 and len(factors)==1:
   i,e=next(iter(factors.items()))
   if e==1:return E(self,i)
  return self.intern(('m',coeff,tuple(sorted(factors.items()))))
class E:
 def __init__(self,r,i):self.r=r;self.i=i
 def __add__(self,b):return self.r.add(self,self.r.coerce(b))
 __radd__=__add__
 def __mul__(self,b):return self.r.mul(self,self.r.coerce(b))
 __rmul__=__mul__
 def __neg__(self):return self*-1
 def __sub__(self,b):return self+-self.r.coerce(b)
 def __rsub__(self,b):return self.r.coerce(b)+-self
 def __pow__(self,k):
  out=self.r.C(1)
  for _ in range(k):out=out*self
  return out
 def __eq__(self,b):return isinstance(b,E) and self.r is b.r and self.i==b.i

def eval_rows(obj,env):
 e=dict(env)
 for name,op,a,b in obj['source']:
  require(name not in e and op in ('+','-','*'),'topology/op')
  require(not isinstance(a,str) or a in e,'unknown first argument')
  require(not isinstance(b,str) or b in e,'unknown second argument')
  x=e[a] if isinstance(a,str) else a;y=e[b] if isinstance(b,str) else b
  e[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return e

def reference(env,which):
 J,F,alpha,i,T,x,Y,n,eta,zeta=[env[z] for z in ['J','F','alpha','i','T','x','Y','n','eta','zeta']]
 beta,K0,MC,MF=[env[z] for z in ['beta','K0','MC','MF']]
 q=beta*J+1;X=q+x;mu=q*q+1;p=mu*Y;Am1=p*(X+1);A=Am1+1
 # Polynomial factorizations equal A^2-1 and v0(v0+1)k^2+1.
 Delta=Am1*(Am1+2);H=4*Am1-1;k=eta+zeta;c=k*Y+eta;v0=p*p*X
 D=v0*k*(v0*k+k)+1;E0=i*c*c;EE=2*E0
 G=(q-1)*(q-F)+alpha;R=G*(q*q-1)+(MC+q*MF)*J;e=k-R-1
 C=q-F-alpha;B=(q*K0+X)*C-q*F;Fs=1+Delta*D*EE*EE;Q=Delta*Delta*D*EE*EE;delta=Q-1
 b=c*(T+alpha)-R;V=Fs*b-c;Dnum=Q*V*V-1;P=q**4*(q-1);M=P*mu*mu*H;Kpos=X*(3*c-2*X)+2
 approx=p*k*(v0*k if which==1 else (v0-p*p)*k)
 S=A*D*EE-E0*approx
 Z=P*mu*mu*(H*(n+V+S-b*B)+Kpos)+H*(mu*mu*(q*(q-1)*Y-q**3*B-(q-1)*X)-P*e)
 ss=delta*Z*Z;u=delta*M*M*D*Fs;v=M*M*Dnum
 return {'N':(ss-u-v)**2-4*u*v,'S':S,'E':EE,'Z':Z,'q':q,'D':D}

def graph_audit(obj,which,prior):
 witnesses=['J','F','alpha','i','T','x','Y','n','eta','zeta'];ports=['beta','K0','MC','MF']
 require(obj['witnesses']==witnesses and obj['fixed_numerals']==ports,'complete input list')
 require(obj['domain']=='strictly positive integers','domain')
 require(obj['coefficient_binding']==prior['coefficient_binding'],'binding unchanged')
 require(obj['parent_sha256']==digest(PKG/'prior/sharp.json'),'parent pin')
 rows=obj['source'];names=[r[0] for r in rows];require(len(names)==len(set(names)),'unique registers')
 r=Ring();env={s:r.S(s) for s in witnesses+ports};actual=eval_rows(obj,env);expected=reference(env,which)
 require(actual['N']==expected['N'],'full free-expression formula')
 require(actual['Cg']==expected['S'] and actual['I']==expected['E'] and actual['Znum']==expected['Z'],'named exact formulas')
 oldenv=dict(env);oldenv['i']=2*env['i'];oldenv['n']=env['n']+actual['Cg'];old=eval_rows(prior,oldenv)
 require(old['N']==actual['N'],'whole old/new polynomial identity')
 require(old['Znum']==actual['Znum'],'whole carrier identity')
 for name in ('Dtau','Df','Q','delta','V','Dnum','Mtot','pair','fa','fc'):
  require(old[name]==actual[name],'shared kernel '+name)
 live={obj['output']}
 for name,op,a,b in reversed(rows):
  if name in live:live.update(v for v in (a,b) if isinstance(v,str))
 require(live==set(names+witnesses+ports),'all gates and inputs live')
 counts=dict(Counter(row[1] for row in rows));require(counts==obj['operation_breakdown'],'operation classes')
 require(len(rows)==obj['operations']==(102 if which==1 else 104),'operation count')
 degrees={s:1 for s in witnesses}|{s:0 for s in ports}
 for name,op,a,b in rows:
  da=degrees[a] if isinstance(a,str) else 0;db=degrees[b] if isinstance(b,str) else 0
  degrees[name]=da+db if op=='*' else max(da,db)
 require(degrees==obj['register_degrees'],'syntactic degree metadata')
 return {'live_operations':len(rows),'operation_breakdown':counts,'all_inputs_live':True,'whole_free_polynomial_identity':True,'independent_closed_formula_identity':True,'canonical_nodes':len(r.nodes)}

def add(a,b,p,sg=1):
 c=[0]*max(len(a),len(b))
 for j,x in enumerate(a):c[j]+=x
 for j,x in enumerate(b):c[j]+=sg*x
 return trim([x%p for x in c])
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def mul(a,b,p):
 c=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  for k,y in enumerate(b):c[j+k]=(c[j+k]+x*y)%p
 return trim(c)
def ray(obj,ports,w,prime):
 env={k:[0,v] for k,v in w.items()}|{k:[v%prime] for k,v in ports.items()}
 for name,op,a,b in obj['source']:
  x=env[a] if isinstance(a,str) else [a];y=env[b] if isinstance(b,str) else [b]
  env[name]=mul(x,y,prime) if op=='*' else add(x,y,prime,1 if op=='+' else -1)
 return env['N']

def main():
 prior=json.loads((PKG/'prior/uncentered.json').read_text());manifest=json.loads((PKG/'MANIFEST.json').read_text())
 for path,h in manifest.items():require(digest(PKG/path)==h,'manifest '+path)
 pins=json.loads((PKG/'SOURCE_PINS.json').read_text())
 for path,h in pins['parent_files'].items():require(digest(PKG/'prior'/path)==h,'parent closure '+path)
 ports={};port_receipt={}
 for name,entry in prior['coefficient_binding']['ports'].items():
  data=(PKG/'coefficients'/entry['file']).read_bytes();raw=gzip.decompress(data)
  require(sha256(data).hexdigest()==entry['gzip_sha256'],'compressed constant '+name)
  require(sha256(raw).hexdigest()==entry['raw_sha256'],'raw constant '+name)
  ports[name]=int.from_bytes(raw,'little');require(ports[name].bit_length()==entry['bits'],'bits '+name)
  require(data==(PKG/'prior/coefficients'/entry['file']).read_bytes(),'whole prior constant '+name)
  port_receipt[name]={'bits':entry['bits'],'sha256':sha256(raw).hexdigest()}
 require(ports['beta']%2==1 and ports['beta']>=31 and ports['K0']>0 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'],'actual constant hypotheses')
 # Free sparse identities are independently verified with SymPy, a standard mathematical library, not a downloaded producer.
 import sympy as sp
 pp,xx,kk,aa,dd,ee,gg=sp.symbols('p X k A D E g')
 vv=pp**2*xx;DD=vv*(vv+1)*kk**2+1;AA=pp*(xx+1)+1
 require(sp.expand(DD-AA*pp*vv*kk**2-(vv*(1-pp**2-pp)*kk**2+1))==0,'first remainder')
 require(sp.expand(DD-AA*pp*(vv-pp**2)*kk**2-((pp**4-pp**3*xx+pp**3+pp**2*xx)*kk**2+1))==0,'second remainder')
 require(sp.expand((aa*dd*ee-gg)*(aa*dd*ee+gg)-(dd*dd*ee*ee-dd)).subs(gg**2,dd*(1+(aa**2-1)*dd*ee**2)).expand()==0,'radical defect identity')
 zz,yy,gg=sp.symbols('Z y g')
 norm=(zz*zz-gg*gg-yy*yy)**2-4*gg*gg*yy*yy
 fact=sp.prod(zz+sg*gg+sy*yy for sg in (-1,1) for sy in (-1,1))
 require(sp.expand(norm-fact)==0,'complete four-factor norm identity')
 q0,X0,Y0,i0,k0,F0=sp.symbols('q0 X0 Y0 i0 k0 F0',nonzero=True)
 a0=q0**2*X0*Y0;d0=q0**8*X0**2*Y0**4*k0**2;e0=i0*k0**2*Y0**2;mask0=q0**3*(q0-F0);p0=q0**2*Y0
 delta0=4*a0**4*d0*e0**2;M0=4*q0**9*a0;V0=-4*a0**2*d0*e0**2*mask0;g0=2*a0*d0*e0
 common=delta0**2*M0**4*(2*V0)**2*(2*g0)
 for which,defect in [(1,-e0*p0**3*k0**2),(2,e0*p0**3*k0**2/X0)]:
  stated=(-1 if which==1 else 1)*2**20*q0**122*X0**(27 if which==1 else 26)*Y0**60*i0**10*k0**32*(q0-F0)**2
  require(sp.cancel(common*defect-stated)==0,'complete symbolic leading form '+str(which))
 receipts={};rng=random.Random(918273);corruptions=[]
 for which,name,degree in [(1,'first',253),(2,'second',252)]:
  obj=json.loads((PKG/(name+'.json')).read_text());receipts[name]=graph_audit(obj,which,prior)
  receipts[name]['sha256']=digest(PKG/(name+'.json'));receipts[name]['degree_from_ordinary_proof']=degree
  rays=[]
  for prime in (2**61-1,2**89-1):
   w={v:rng.randrange(1,30) for v in obj['witnesses']};f=ray(obj,ports,w,prime)
   q0=ports['beta']%prime*w['J'];X0=q0+w['x'];k0=w['eta']+w['zeta']
   top=(-1 if which==1 else 1)*pow(2,20,prime)*pow(q0,122,prime)*pow(X0,27 if which==1 else 26,prime)*pow(w['Y'],60,prime)*pow(w['i'],10,prime)*pow(k0,32,prime)*pow(q0-w['F'],2,prime)%prime
   require(len(f)-1==degree and f[-1]==top,'full modular polynomial / top coefficient')
   rays.append({'prime':str(prime),'actual_degree':len(f)-1,'top_coefficient_matches':True})
  receipts[name]['supplementary_modular_polynomial_rays']=rays
  mutations=[]
  m=deepcopy(obj);next(r for r in m['source'] if r[0]=='I')[2]=3;mutations.append(('wrong_even_factor',m))
  m=deepcopy(obj);next(r for r in m['source'] if r[0]=='Cg')[1]='+';mutations.append(('wrong_center_sign',m))
  m=deepcopy(obj);next(r for r in m['source'] if r[0]=='correction')[3]='i';mutations.append(('wrong_correction_operand',m))
  m=deepcopy(obj);m['source'].append(['dead','+',1,2]);mutations.append(('dead_gate',m))
  m=deepcopy(obj);m['coefficient_binding']['ports']['MF']['bits']-=1;mutations.append(('changed_coefficient_binding',m))
  for label,mut in mutations:
   try:graph_audit(mut,which,prior)
   except (ValueError,KeyError):corruptions.append(name+':'+label)
   else:raise ValueError('corruption escaped '+label)
 receipt={'status':'PASS','scope':'Independent free-expression whole-DAG/formula/old-polynomial identities, local free-ring remainders, all source/constant hashes, live census, supplementary full modular ray polynomials. Ordinary universal proof reviewed separately. No producer imports or execution.', 'manifest_files_checked':len(manifest),'parent_source_files_checked':len(pins['parent_files']),'constants':port_receipt,'candidates':receipts,'corruptions_rejected':corruptions}
 (HERE/'AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
