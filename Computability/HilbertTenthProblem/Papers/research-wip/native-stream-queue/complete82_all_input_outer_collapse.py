#!/usr/bin/env python3
"""Literal full82 source plus exact component checks for the all-input collapse.
No predecessor code is imported or executed. The unbounded proof is in the note.
"""
import argparse,copy,hashlib,json
from collections import Counter
from pathlib import Path
PINS={
 'complete82_auxiliary_square_product_chart.py':'5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc',
 'complete82_auxiliary_square_product_chart.json':'7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a',
 'complete82_auxiliary_square_product_chart.md':'10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9',
 'complete75_weakened86_infinite_outer_family.md':'74b6c968500c5177440096bd3da3c9c07f9208f10aea79cad73554e9814bf1a2',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_weakened86_rejecting_compiler.md':'186fc8a89c99455361fd0eb0b90d53c1fa90af32191a741c02e950d3bb0d8e78'}
def check(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def pairs(ps):
 d={}
 for k,v in ps:check(k not in d,'duplicate JSON key');d[k]=v
 return d
def read(p):return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
class Poly:
 def __init__(self,v=0):
  if type(v)is Poly:self.c=dict(v.c)
  elif type(v)is dict:self.c={m:z for m,z in v.items() if z}
  else:self.c={():v} if v else {}
 def __add__(self,b):
  d=dict(self.c)
  for m,v in Poly(b).c.items():d[m]=d.get(m,0)+v
  return Poly(d)
 __radd__=__add__
 def __neg__(self):return Poly({m:-v for m,v in self.c.items()})
 def __sub__(self,b):return self+-Poly(b)
 def __rsub__(self,b):return Poly(b)+-self
 def __mul__(self,b):
  d={}
  for m,v in self.c.items():
   for n,w in Poly(b).c.items():
    k=tuple(sorted(m+n));d[k]=d.get(k,0)+v*w
  return Poly(d)
 __rmul__=__mul__
 def __pow__(self,n):
  z=Poly(1)
  for _ in range(n):z=z*self
  return z
 def __eq__(self,b):return self.c==Poly(b).c

def var(x):return Poly({(x,):1})
def op(o,a,b):return a+b if o=='+' else a-b if o=='-' else a*b

def audit(p):
 seen=set(p['free']);check(len(seen)==25 and len(p['witnesses'])==18,'interface')
 parents={};counts=Counter()
 for d,o,a,b in p['source']:
  check(d not in seen and o in ('+','-','*'),'SSA/operator')
  for x in (a,b):check(type(x)is int or type(x)is str and x in seen,'closure')
  parents[d]=[x for x in (a,b) if type(x)is str];seen.add(d);counts[o]+=1
 live={p['output']};pending=list(live)
 while pending:
  for x in parents.get(pending.pop(),[]):
   if x not in live:live.add(x);pending.append(x)
 check(live==seen,'all gates and ports live')
 ledger={'M':counts['*'],'A':counts['+']+counts['-'],'total':sum(counts.values())}
 check(ledger=={'M':45,'A':37,'total':82},'full82 paid source')
 check(p['exact_degree']==185,'inherited exact degree')
 return ledger

def cone(p,port,bindings):
 rows={d:(o,a,b) for d,o,a,b in p['source']};env=dict(bindings)
 def rec(x):
  if type(x)is int:return Poly(x)
  if x not in env:
   if x in rows:
    o,a,b=rows[x];env[x]=op(o,rec(a),rec(b))
   else:env[x]=var(x)
  return env[x]
 return rec(port)

def symbolic(p):
 q=var('Bm1')*var('Jrep')+1;K=var('Kconstant');W=var('W_value');lx=var('twice_cell_bits')*var('x')
 C=W+1;F=(K+1)*C
 bindings={'F':F,'Z':Poly(1),'alpha':q-F-W-lx-2,
  'transport_quotient':(q+1)*C+1,'w':q*q,'s':Poly(1)}
 targets={'q':q,'wn2':q**3,'sn2':q**3,'UM':q**6,
  'marked_rhs':C,'W':W,'odd_index':lx+var('inner_bits'),
  'r_lhs':(q*(q-F)-1)*(q*q-1)+(var('MC')+q*var('MF'))*var('Jrep'),
  'norm_transport':Poly(1)}
 for name,value in targets.items():check(cone(p,name,bindings)==value,'literal outer '+name)
 X,Y,z,c,a,H,D,kappa,rho,gamma,V,y,R,Faux,U,Delta=[var(x) for x in ['X','Y','z','c','a','H','D','kappa','rho','gamma','V','y','R','Faux','U','Delta']]
 tau=var('tau');P=2*X*Y*Y+1;k=2*z
 ratio_bind={'wn2':X,'sn2':Y,'eta':c-k*Y,'zeta':k*(Y+1)-c,'tau_root':tau}
 check(cone(p,'R10b',ratio_bind)==k,'two slacks restore k')
 check(cone(p,'R10a',ratio_bind)==c,'two slacks restore c')
 check(cone(p,'norm_first',ratio_bind)==tau*tau-(P*P-1)*z*z,'literal first Pell factor')
 roots={'wn2':X,'R12':a,'R10a':c,'a4m5':H,'rho':rho,'sigma':gamma-rho}
 check(cone(p,'R14',roots)==X+a*c+gamma*H,'main quotient definition')
 check(cone(p,'exponent_rhs',{'W':W,'R12':a,'index_rhs':kappa,'rho':rho,'a4m5':H})==W+a*kappa+rho*H,'input quotient definition')
 check(cone(p,'norm_main',{'R14':D,'A':Delta,'R10a':c})==D*D-Delta*c*c,'main Pell factor')
 check(cone(p,'norm_input',{'exponent_rhs':D,'A':Delta,'index_rhs':kappa})==D*D-Delta*kappa*kappa,'input Pell factor')
 check(cone(p,'norm_index',{'R10b':k,'h':var('h'),'UM':var('E'),'r_lhs':R})==k-var('h')*var('E')-R,'index factor')
 aux={'i':Poly(1),'A':Delta,'R10a':c,'L16':Faux,'auxiliary_Tf':U,'r_lhs':R,'y_aux':y}
 check(cone(p,'aux_u_rhs',aux)==c*(U-1)-R*Faux,'aux quotient interface')
 check(cone(p,'norm_strong',dict(aux,L16=Delta*c**4+1))==Delta,'scaled strong Delta')
 check(cone(p,'norm_aux',dict(aux,aux_u_rhs=V))==(Delta*c*c)**2*(V*V-y*y)+y*y,'aux Pell factor')
 factor_ports={f:Poly(1) for f in p['factors']};factor_ports['norm_strong']=Delta;factor_ports['A']=Delta
 check(cone(p,p['output'],factor_ports)==0,'complete paid finalizer')
 # Independent derivation of the positive integer input-quotient recurrence.
 aa,rn,rm,b=map(var,('baseA','rho_n','rho_prev','pow2_prev'));hh=4*aa-5
 En=2*b+hh*rn;Em=b+hh*rm;Enext=4*b+hh*(2*aa*rn-rm+b)
 check(Enext==2*aa*En-Em,'input quotient recurrence')
 return {'outer_port_identities':len(targets),'ratio_root_norm_index_aux_finalizer_identities':12,
  'input_quotient_recurrence':True,'all_coefficient_identities_exact':True}

def pell(A,n,mod=None):
 delta=A*A-1;z=(1,0);b=(A,1)
 def mul(x,y):
  t=(x[0]*y[0]+delta*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
  return tuple(v%mod for v in t) if mod else t
 while n:
  if n&1:z=mul(z,b)
  b=mul(b,b);n//=2
 return z

def outer_input_fixtures(p):
 records=[]
 for x,b,K in [(1,1,2),(1,1,4),(1,5,10),(2,1,2),(2,1,4)]:
  d=5;B=2**d;N=5;q=B**N;J=(q-1)//(B-1);u=2*d*x+b;W=2**u;C=W+1;F=(K+1)*C;MC=2;MF0=4;MF=MF0+B-1
  check(q>F+W+2*d*x+2,'toy outer margin')
  alpha=q-F-W-2*d*x-2;t=(q+1)*C+1;Z=1;X=Y=q**3;E=X*Y;a=Y*(X+1);A=a+2;Delta=A*A-1;H=4*a+3;P=2*X*Y*Y+1
  R=(q*(q-F)-1)*(q*q-1)+(MC+q*MF)*J
  vals={'F':F,'Z':Z,'alpha':alpha,'transport_quotient':t,'w':q*q,'s':1,'x':x,'Bm1':B-1,'Jrep':J,'Kconstant':K,'twice_cell_bits':2*d,'inner_bits':b,'MC':MC,'MF':MF}
  numeric={k:Poly(v) for k,v in vals.items()}
  for name,want in [('marked_rhs',C),('W',W),('norm_transport',1),('r_lhs',R)]:check(cone(p,name,numeric)==want,'actual outer fixture '+name)
  check(0<R<q**4 and R%2==1 and R+1<E,'packing and first-index range')
  chi,kap=pell(A,u);check((kap-u)%Delta==0 and kap>u,'positive input delta')
  ep=chi-a*kap;check((ep-W)%H==0 and ep>W,'positive input rho')
  rho=(ep-W)//H;delta=(kap-u)//Delta
  check(kap==2*d*x+b+delta*Delta and W+a*kap+rho*H==chi,'actual input roots')
  check(chi*chi-Delta*kap*kap==1,'actual input norm')
  n0=(R+1)//2;check(2*pell(P,n0,E)[1]%E==(R+1)%E,'actual fixed index residue')
  e=3*d*N;Dm,c=pell(A,e);g=(Dm-a*c-X)//H
  check((Dm-a*c-X)%H==0 and g>rho and c%2==1,'positive main residue component')
  check(Dm*Dm-Delta*c*c==1,'main norm component')
  records.append({'x':x,'b':b,'K':K,'d':d,'N':N,'q':q,'alpha':alpha,'F':F,'C':C,'W':W,'R':str(R),
   'input_index':u,'input_delta_bits':delta.bit_length(),'input_rho_bits':rho.bit_length(),
   'main_component_index':e,'main_c_bits':c.bit_length(),
   'scope':'Necessary-parameter toy slice only, not certified compiler numerals. Outer/input/main components and index residue pass separately; no first/main ratio or full zero is claimed.'})
 return records

def small_period_fixtures():
 records=[]
 for A in (2,4,6,8,10,12):
  a=A-2;H=4*A-5;Delta=A*A-1;L=1
  while pow(2,L,H)!=1:L+=1;check(L<=H,'finite period')
  rprev=0;rnow=0
  for n in range(1,12):
   rnext=2*A*rnow-rprev+2**(n-1);rprev,rnow=rnow,rnext
   v=n+1;ch,ps=pell(A,v);check(ch-a*ps==2**v+H*rnow and rnow>rprev,'quotient recurrence positive')
  for u in (3,5,7):
   ch,ps=pell(A,u);check((ps-u)%Delta==0 and ps>u,'odd input residue')
  for r in (1,2,3):
   p=3+4*L*r;ch,c=pell(A,p);check((ch-a*c-8)%H==0 and c%2==1,'odd main period')
  records.append({'A':A,'H':H,'power_return':L,'quotient_indices':list(range(2,13)),'main_progression_steps':[1,2,3]})
 return records

def auxiliary_fixtures():
 records=[]
 for A in (2,3,5):
  Delta=A*A-1;c=pell(A,3)[1];S=Delta*c*c;Faux=Delta*c**4+1
  for R in (1,3,7):
   v=next(R+j*c for j in range(4) if (R+j*c)%4==3)
   ch,y=pell(S,v);check(ch%S==0,'odd aux quotient');V=ch//S
   check((V+R*Faux)%c==0,'aux U integrality');U=(V+R*Faux)//c+1
   check(U>0 and c*(U-1)-R*Faux==V,'actual aux coordinate')
   check(S*S*(V*V-y*y)+y*y==1 and Delta*Faux-S*S==Delta,'actual auxiliary/strong factors')
   records.append({'A':A,'c':c,'R':R,'v_aux':v,'F_aux':Faux,'U_bits':U.bit_length(),'y_bits':y.bit_length(),
    'scope':'Complete auxiliary block only; no full compiler tuple.'})
 return records

def verify(root):
 for f,h in PINS.items():check(sha(root/f)==h,'pin '+f)
 parent=read(root/'complete82_auxiliary_square_product_chart.json');p=copy.deepcopy(parent['packet'])
 check(parent['source_sha256']==PINS['complete82_auxiliary_square_product_chart.py'],'parent self-source pin')
 inherited=parent['dependency_pins']
 for f,h in inherited.items():check(sha(root/f)==h,'inherited dependency '+f)
 ledger=audit(p);proof=symbolic(p)
 p['universal_soundness']='REFUTED: every positive input has infinitely many positive zeros on every inherited valid fixed-program slice.'
 return {'status':'PASS','source_sha256':sha(Path(__file__)),'dependency_pins':PINS,'inherited_parent_pins':inherited,
  'packet':p,'source_unchanged':True,'ledger':ledger,'exact_degree':185,
  'symbolic':proof,'outer_input_main_components':outer_input_fixtures(p),'small_period_components':small_period_fixtures(),
  'auxiliary_components':auxiliary_fixtures(),
  'theorem':'Every positive ordinary input on every inherited valid compiler slice has infinitely many full positive zeros of the unchanged82 source.',
  'retained_factor_values':['1','1','1','1','1'],'all_factor_values':['1','1','1','1','1','1','Delta'],
  'full_compiler_zero_materialized':False,'existence_dependency':'Irrational rotation plus the exact Pell conjugate-error estimate; no prime theorem is needed.',
  'established_universal_bound':84}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path)
 mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument('--output',type=Path);mode.add_argument('--expect',type=Path)
 a=ap.parse_args();r=verify(a.root)
 if a.expect:check(exact(r,read(a.expect)),'exact typed receipt')
 else:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print('PASS: full82 source; exact outer/norm/finalizer cuts; five outer/input component fixtures; nine auxiliary blocks. No full compiler zero materialized.')
if __name__=='__main__':main()
