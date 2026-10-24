"""Authored exact algebra check and literal packet builder; never imports upstream code."""
import ast,json,hashlib
from pathlib import Path
import sympy as S
ROOT=Path(__file__).resolve().parent

def parse(t,env):
 n=ast.parse(t,mode='eval').body
 def f(a):
  if isinstance(a,ast.Constant) and isinstance(a.value,int): return S.Integer(a.value)
  if isinstance(a,ast.Name) and a.id in env:return env[a.id]
  if isinstance(a,ast.UnaryOp) and isinstance(a.op,ast.USub):return -f(a.operand)
  if isinstance(a,ast.BinOp):
   l,r=f(a.left),f(a.right)
   if isinstance(a.op,ast.Add):return l+r
   if isinstance(a.op,ast.Sub):return l-r
   if isinstance(a.op,ast.Mult):return l*r
   if isinstance(a.op,ast.Pow) and isinstance(r,S.Integer) and 0<=r<=20:return l**r
  raise ValueError(ast.dump(a))
 return S.expand(f(n))

def req(b,msg):
 if not b:raise ValueError(msg)
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
p=ROOT/'inherited/quartic38.json';src=json.loads(p.read_text())
ports=['beta','K0','MC','MF','cone_A','cone_B']
names=src['variables']+ports+['J3','w3','X3','C','t','p','qpos','rpos']
e={n:S.Symbol(n) for n in names};vs=[e[n] for n in src['variables']]
r=[parse(t,e) for t in src['residuals']]
J,F,alpha,z,f,h,rr,v,w,tau,eta,zeta,y,gamma,o,j,N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta,u=[e[n] for n in src['variables'][:32]]
beta,K0,MC,MF,AA,BB=[e[n] for n in ports]
J3,w3,X3,C,t,pv,qv,rv=[e[n] for n in ['J3','w3','X3','C','t','p','qpos','rpos']]
q=beta*J+1;k=eta+zeta;H=4*a+3
cone=AA*F*BB*(q-F-alpha)-(q-AA*F-BB*(q-F-alpha))**2
Pos=lambda p,q,r:1+p*p+q*q+r*(r+1)
req(S.expand(r[23]-(cone-Pos(e['cone_pos1'],e['cone_pos2'],e['cone_pos3'])))==0,'cone literal')
req(r[22]==X-2*u*u,'deleted row')
req(S.expand(r[24]-(eta*zeta-Pos(e['eta_zeta_pos1'],e['eta_zeta_pos2'],e['eta_zeta_pos3'])))==0,'eta guard')

def degree(r,vs):return S.Poly(r,*vs).total_degree()
def packet(name,vs,rs,degree_expected,cert,extra=None):
 rs=[S.expand(x) for x in rs]
 degrees=[int(degree(x,vs)) for x in rs]
 req(2*max(degrees)==degree_expected,name+' degree')
 req(set().union(*(x.free_symbols for x in rs))-set(map(e.get,ports))==set(vs),name+' liveness')
 cm={e[n]:v for n,v in cert.items()}; target=tuple(cm.get(x,0) for x in vs)
 co=S.Integer(0)
 for residual in rs:
  terms=S.Poly(residual,*vs).as_dict()
  for m,c0 in terms.items():
   other=tuple(a-b for a,b in zip(target,m))
   if min(other)>=0:co+=c0*terms.get(other,0)
 co=S.factor(co)
 req(co!=0 and co.free_symbols<=set(e[n] for n in ports),name+' cert')
 cp=S.Poly(co,*[e[n] for n in ports])
 req(all(c>0 for c in cp.coeffs()),name+' positive coefficient certificate')
 out=dict(name=name,domain='unrestricted integers',variables=list(map(str,vs)),variable_count=len(vs),fixed_numerals=ports,residuals=list(map(str,rs)),equation_count=len(rs),residual_degrees=degrees,single_polynomial='sum of squared residuals',exact_degree=degree_expected,degree_certificate={'monomial':cert,'coefficient':str(co)},coefficient_binding='BINDING.json',proof='PROOF.md',source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 if extra:out.update(extra)
 dump(ROOT/(name+'.json'),out)
 return vs,rs

# Direct smaller quartic for expression size.
rd=[S.expand(v.subs(X,3*X3-1)) for i,v in enumerate(r) if i!=22]
vd=[X3 if v==X else v for v in vs if v!=u]
packet('quartic37_direct',vd,rd,4,{'tau':4})
# Affine restrictions retain a monic X and make projections integral.
aff={J:3*J3+1,w:3*w3+1}; qa=beta*(3*J3+1)+1;Wa=4*(3*w3+1)
ra=[S.expand(v.subs(aff)) for i,v in enumerate(r) if i!=22]
va=[J3 if v==J else w3 if v==w else v for v in vs if v!=u]
packet('quartic37',va,ra,4,{'tau':4})
# Simultaneously center two roots and retain f-square as a lifting register.
restore={P:k+E*(c-eta),X:Wa*qa,N:qa*(L+1),C2:c*c,Delta:a*a+4*a+3,V:f*o-c,Baux:I*I,tau:tau+E*(c-eta),D:D+a*c}
rs=[S.expand(x.subs(restore,simultaneous=True)) for x in ra]
zero=[i for i,x in enumerate(rs) if x==0]
req(zero==[1,2,6,9,10,15,19],str(zero))
# Replace f^2 o^2 by F2 o^2 modulo its retained definition.
rs[17]=S.expand(rs[17]+o*o*(F2-f*f))
v30=[v for v in va if v not in [P,X,N,C2,Delta,V,Baux]]
packet('sextic30',v30,[x for x in rs if x!=0],6,{'I':4,'g':2}, {'restoration':{str(v):str(x) for v,x in restore.items()},'row_correction':'source difference row plus o**2*(F2-f**2)'})
# The quartic-residual projection.
k0=1-V+j*c+h*E
ro={L:qa**2-1,N:qa**3,X:Wa*qa,C2:c*c,F2:f*f,g:y*y-V*V,Baux:I*I,D:Wa*qa+a*c+gamma*(4*a+3),Delta:a*a+4*a+3,zeta:k0-eta,P:k0+E*(c-eta)}
rrs=[S.expand(x.subs(ro,simultaneous=True)) for x in ra]
req(sum(x==0 for x in rrs)==11,'octic deletes')
v26=[v for v in va if v not in ro]
r26=[x for x in rrs if x!=0]
packet('octic26',v26,r26,8,{'a':4,'f':4},{'restoration':{str(v):str(x) for v,x in ro.items()}})
# Last two positivity rows are existentially replaced by nearest-square guard.
guards=[e[n] for n in ['cone_pos1','cone_pos2','cone_pos3','eta_zeta_pos1','eta_zeta_pos2','eta_zeta_pos3']]
xcone=S.expand(cone.subs(aff)); yz=S.expand(eta*(k0-eta))
req(S.expand(r26[-2]-(xcone-Pos(*guards[:3])))==0,'cone projection')
req(S.expand(r26[-1]-(yz-Pos(*guards[3:])))==0,'eta projection')
G=lambda x,y,t:x*y-(t*t-x-y+1)**2
vj=[v for v in v26 if v not in guards]+[t,pv,qv,rv]
rj=r26[:-2]+[G(xcone,yz,t)-Pos(pv,qv,rv)]
packet('degree12_24',vj,rj,12,{'eta':4,'j':4,'c':4})
# Pivot transport using the complement coordinate; it costs degree, not integrality.
Frestore=(K0+Wa)*C-z*(qa-1)
tr={F:Frestore,alpha:qa-Frestore-C}
r25=[S.expand(x.subs(tr,simultaneous=True)) for x in r26]
req(sum(x==0 for x in r25)==1,'transport pivot')
v25=[C if v==alpha else v for v in v26 if v!=F]
packet('degree10_25',v25,[x for x in r25 if x!=0],10,{'w3':2,'C':2,'J3':6},{'restoration':{str(v):str(x) for v,x in tr.items()}})
r23=[S.expand(x.subs(tr,simultaneous=True)) for x in rj]
v23=[C if v==alpha else v for v in vj if v!=F]
packet('degree16_23',v23,[x for x in r23 if x!=0],16,{'w3':8,'C':8})
print('All seven literal packets built with exact symbolic checks')
