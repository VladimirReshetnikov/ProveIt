"""Bounded source-pinned joint-norm evaluation scout; no improved bound claimed."""
from collections import Counter
from pathlib import Path
import argparse,hashlib,json,random
import sympy as sp

PINS={'complete75_asymmetric_scale_tradeoffs.py': 'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660', 'complete75_asymmetric_scale_tradeoffs.json': '47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98', 'complete75_normalized_strong87.py': '7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8', 'complete75_coupled_index_linear88.py': 'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749'}
WITNESSES=['Jrep','F','alpha','zplus','f','h','i','j','o','s','w','tau_gap','eta','zeta','y_aux','Z','delta','rho','sigma']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(v,m):
 if not v:raise ValueError(m)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def source(root):
 for n,h in PINS.items():need(digest(root/n)==h,'Source pin '+n)
 d=json.loads((root/'complete75_asymmetric_scale_tradeoffs.json').read_text())
 r=d['source'][0]['source'];need(len(r)==87 and d['source'][0]['normalized'] is True,'Selected normalized source')
 return [tuple(x) for x in r]
def closure(rows):
 names={n for n,*_ in rows};free={v for _,_,a,b in rows for v in (a,b) if type(v) is str and v not in names}
 available=set(free)
 for n,op,a,b in rows:
  need(n not in available and op in ('+','-','*'),'Malformed gate')
  need(all(type(x) is int or x in available for x in (a,b)),'Missing operand');available.add(n)
 nodes={n:(op,a,b) for n,op,a,b in rows};live=set()
 def visit(x):
  if type(x) is int or x in free or x in live:return
  need(x in nodes,'Unknown dependency');live.add(x)
  for y in nodes[x][1:]:visit(y)
 visit('polynomial');need(live==names,'Dead source row');need(set(WITNESSES+['x'])<=free,'Lost witness/input')
 return sorted(free)
def prune(nodes):
 rows=[];done=set();active=set()
 def visit(n):
  if type(n) is int or n not in nodes or n in done:return
  need(n not in active,'Cycle');active.add(n);op,a,b=nodes[n];visit(a);visit(b);rows.append((n,op,a,b));active.remove(n);done.add(n)
 visit('polynomial');closure(rows);return rows

def rewrite(old,kind):
 d={n:(op,a,b) for n,op,a,b in old}
 if kind=='direct_norm_composition':
  d.update(j_ck=('*','R10a','index_rhs'),j_dck=('*','A','j_ck'),j_Dmu=('*','R14','exponent_rhs'),j_u=('-','j_Dmu','j_dck'),j_Dk=('*','R14','index_rhs'),j_muc=('*','exponent_rhs','R10a'),j_v=('-','j_Dk','j_muc'))
 elif kind=='expanded_norm_composition':
  # D=a*c+l, mu=a*kappa+m, Delta=a*a+H.
  d.update(j_l=('+','wn2','gam'),j_m=('+','W','modulus_multiple'),j_cm=('*','R10a','j_m'),j_kl=('*','index_rhs','j_l'),j_v=('-','j_kl','j_cm'),j_sum=('+','j_cm','j_kl'),j_asum=('*','R12','j_sum'),j_lm=('*','j_l','j_m'),j_ck=('*','R10a','index_rhs'),j_Hck=('*','a4m5','j_ck'),j_upart=('+','j_asum','j_lm'),j_u=('-','j_upart','j_Hck'))
 elif kind=='auxiliary_strong_unit_substitution':
  d['j_fminus']=('-','L16',1);d['R16']=('*','A','j_fminus')
 elif kind=='first_norm_reassociation':
  d['j_twobase']=('+','first_root_base','first_root_base')
  d['j_firstsum']=('+','tau_gap','j_twobase')
  d['j_firstprod']=('*','tau_gap','j_firstsum')
  d['j_Uk']=('*','first_root_base','R10b')
  d['norm_first']=('-','j_firstprod','j_Uk')
 else:raise ValueError('Unknown exact scout family')
 if 'composition' in kind:
  d.update(j_u2=('*','j_u','j_u'),j_v2=('*','j_v','j_v'),j_Dv2=('*','A','j_v2'),j_joint=('-','j_u2','j_Dv2'))
  d['norm_triple']=('*','norm_first','j_joint')
 return prune(d)
def run(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=a if type(a) is int else e[a];b=b if type(b) is int else e[b]
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e

def symbolic():
 D,mu,c,k,Delta,a,H,l,m,g,U,f,t,V,y,P=sp.symbols('D mu c k Delta a H l m g U f t V y P')
 Nm=D**2-Delta*c**2;Ni=mu**2-Delta*k**2
 need(sp.expand((D*mu-Delta*c*k)**2-Delta*(D*k-mu*c)**2-Nm*Ni)==0,'Norm composition')
 uu=a*(c*m+k*l)+l*m-H*c*k;vv=k*l-c*m
 need(sp.expand((D*mu-Delta*c*k).subs({D:a*c+l,mu:a*k+m,Delta:a*a+H})-uu)==0,'Expanded root')
 need(sp.expand((D*k-mu*c).subs({D:a*c+l,mu:a*k+m})-vv)==0,'Expanded ordinate')
 need(sp.expand(g*g+U*(2*g-k)-(g*(g+2*U)-U*k))==0,'First norm reassociation')
 Ns=f*f-Delta*t*t;Na=Delta**2*t*t*(V*V-y*y)+y*y;Nb=Delta*(f*f-1)*(V*V-y*y)+y*y
 need(sp.expand(P*Ns*Nb-P*Ns*Na-P*Ns*Delta*(Ns-1)*(V*V-y*y))==0,'Full substituted-aux correction')
 residues=[]
 for a0 in range(4):
  for f0 in range(4):
   for t0 in range(4):
    n=(f0*f0-((a0+2)**2-1)*t0*t0)%4;need(n!=3,'Negative strong unit');residues.append(n)
 return {'exact_symbolic_identities':5,'negative_strong_unit_mod4_cases':len(residues)}
def verify(root):
 old=source(root);free=closure(old);rng=random.Random(871690604);sym=symbolic();forms=[]
 expected={'first_norm_reassociation':87,'direct_norm_composition':90,'expanded_norm_composition':89,'auxiliary_strong_unit_substitution':88}
 for kind,cost in expected.items():
  rows=rewrite(old,kind);need(closure(rows)==free,'Changed complete free-coordinate interface');need(len(rows)==cost,'Unexpected complete cost');count=Counter(op for _,op,_,_ in rows);signed=0
  for case in range(256):
   v={n:rng.randrange(-4,5) if case%2 else rng.randrange(1,5) for n in WITNESSES+['x']};B=(16,32,64,128)[case%4]
   v.update(Bm1=B-1,Kconstant=3+B*5,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=4+B-1)
   need(set(free)<=v.keys(),'Paid fixed constants supplied')
   before=run(old,v);after=run(rows,v)
   if kind=='auxiliary_strong_unit_substitution':
    remainder=1
    for f in FACTORS:
     if f not in ('norm_aux','norm_strong'):remainder*=before[f]
    correction=remainder*before['norm_strong']*before['A']*(before['norm_strong']-1)*before['aux_square_gap']
    need(after['polynomial']-before['polynomial']==correction,'Complete off-zero correction')
   else:need(after['polynomial']==before['polynomial'],'Complete all-value identity')
   signed+=case%2
  forms.append({'kind':kind,'operations':len(rows),'M':count['*'],'A':count['+']+count['-'],'complete_source':rows,'output':'polynomial','witnesses':19,'ordinary_input':'x','all_gates_live':True,'identical_free_coordinates':free,'complete_numeric_cases':256,'signed_cases':signed,'scope':'Same entire polynomial' if kind!='auxiliary_strong_unit_substitution' else 'Exact recorded correction; same full integer zero sets by unconditional strong-factor negative-unit exclusion'})
 return {'status':'PASS_NO_OPERATION_IMPROVEMENT','source_pins':PINS,'baseline':{'operations':87,'M':48,'A':39,'degree':169,'witnesses':19},'symbolic':sym,'forms':forms,'scope':'Four explicit complete schedules, not an exhaustive circuit search or a general87 lower bound. Every input, scale, ratio and strong condition is retained. No giant universal zero is materialized.'}

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);args=a.parse_args();result=verify(args.root.resolve());result=json.loads(json.dumps(result))
 if args.expect:need(exact(result,json.loads(args.expect.read_text())),'Receipt mismatch')
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(result['status']);print([(r['kind'],r['operations'],r['M'],r['A']) for r in result['forms']])
