#!/usr/bin/env python3
"""Auxiliary-ordinate sum/excess coordinates: bounded complete87 scout.

Reads only authenticated parent JSON and source bytes; no parent imports.
Six exact evaluation templates for each of two coordinate automorphisms.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import sympy as sp

PINS = {
 'complete75_asymmetric_scale_tradeoffs.py':'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660',
 'complete75_asymmetric_scale_tradeoffs.json':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98',
 'complete75_normalized_strong87.py':'7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8',
 'complete75_coupled_index_linear88.py':'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed',
 'complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
}
WITNESSES=['Jrep','F','alpha','zplus','f','h','i','j','o','s','w','tau_gap','eta','zeta','y_aux','Z','delta','rho','sigma']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
TEMPLATES=['restore','shifted_square','factored_gap','folded_coefficient','expanded_cross','difference_product']


def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def source(root):
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'parent source pin '+n)
 record=json.loads((root/'complete75_asymmetric_scale_tradeoffs.json').read_text())['source'][0]
 need(record['normalized'] is True,'wrong parent treatment')
 rows=[tuple(v) for v in record['source']]
 need(len(rows)==87,'wrong complete parent count')
 return rows

def run(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e

def inspect(rows):
 names={r[0] for r in rows};need(len(names)==len(rows),'duplicate source register')
 free={v for _,_,a,b in rows for v in(a,b) if type(v)is str and v not in names}
 available=set(free)
 for n,op,a,b in rows:
  need(type(n)is str and op in('+','-','*') and n not in available,'malformed instruction')
  need(all(type(v)is int or(type(v)is str and v in available) for v in(a,b)),'bad operand')
  available.add(n)
 nodes={n:(a,b) for n,_,a,b in rows};live=set()
 def visit(v):
  if type(v)is int or v in free or v in live:return
  need(v in nodes,'unknown source');live.add(v)
  for u in nodes[v]:visit(u)
 visit('polynomial');need(live==names,'dead gate')
 counts=Counter(op for _,op,_,_ in rows)
 return {'operations':len(rows),'M':counts['*'],'A':counts['+']+counts['-'],'free':sorted(free),'all_gates_live':True}

def prune(nodes):
 rows=[];done=set();active=set()
 def visit(v):
  if type(v)is int or v not in nodes or v in done:return
  need(v not in active,'cycle');active.add(v)
  op,a,b=nodes[v];visit(a);visit(b)
  rows.append((v,op,a,b));done.add(v);active.remove(v)
 visit('polynomial');return rows

def rewrite(old,eps,template):
 need(type(eps)is int and eps in(-1,1),'bad coordinate sign')
 need(template in TEMPLATES,'bad template')
 nodes={n:(op,a,b) for n,op,a,b in old};new={}
 def gate(n,op,a,b):
  n='excess_'+n;need(n not in nodes,'name collision');nodes[n]=(op,a,b);new[n]=(op,a,b);return n
 V,K,e='aux_u_rhs','R16','y_aux'
 def shift(n,a,b):return gate(n,'+' if eps==1 else '-',a,b)
 if template=='restore':
  y=shift('restore_y',e,V);v2=gate('v2','*',V,V);y2=gate('y2','*',y,y)
  gap=gate('gap','-',v2,y2);term=gate('term','*',K,gap);out=gate('norm','+',term,y2)
 elif template=='shifted_square':
  y=shift('restore_y',e,V);y2=gate('y2','*',y,y)
  twice=gate('twice_v','+',V,V);line=shift('line',e,twice)
  p=gate('gap','*',e,line);scaled=gate('scaled','*',K,p);out=gate('norm','-',y2,scaled)
 elif template=='factored_gap':
  v2=gate('v2','*',V,V);km1=gate('km1','-',K,1)
  twice=gate('twice_v','+',V,V);line=shift('line',e,twice)
  p=gate('gap','*',e,line);scaled=gate('scaled','*',km1,p);out=gate('norm','-',v2,scaled)
 elif template=='folded_coefficient':
  v2=gate('v2','*',V,V);ke=gate('ke','*',K,e);diff=gate('difference','-',e,ke)
  twice=gate('twice_v','+',V,V);line=shift('line',e,twice)
  term=gate('term','*',diff,line);out=gate('norm','+',v2,term)
 elif template=='expanded_cross':
  v2=gate('v2','*',V,V);coeff=gate('coefficient','-',1,K);e2=gate('e2','*',e,e)
  ve=gate('ve','*',V,e);twice=gate('twice_ve','+',ve,ve);line=shift('line',e2,twice)
  term=gate('term','*',coeff,line);out=gate('norm','+',v2,term)
 else:
  y=shift('restore_y',e,V);y2=gate('y2','*',y,y)
  lo=gate('low','-',y,V);hi=gate('high','+',y,V);p=gate('gap','*',lo,hi)
  scaled=gate('scaled','*',K,p);out=gate('norm','-',y2,scaled)
 # A zero-cost alias exists only in this construction dictionary, never in the
 # paid emitted source. Replace all consumers and prune the old aux block.
 for n,(op,a,b) in list(nodes.items()):
  if n not in new:nodes[n]=(op,out if a=='norm_aux' else a,out if b=='norm_aux' else b)
 rows=prune(nodes)
 return rows,new,out

def cse(rows):
 aliases={};seen={};result=[]
 def key(v):return (0,v) if type(v)is int else(1,v)
 for n,op,a,b in rows:
  a=aliases.get(a,a);b=aliases.get(b,b)
  if op in('+','*') and key(b)<key(a):a,b=b,a
  value=None
  if type(a)is int and type(b)is int:value=a+b if op=='+' else a-b if op=='-' else a*b
  elif op=='+' and a==0:value=b
  elif op=='-' and b==0:value=a
  elif op=='*' and a==0:value=0
  elif op=='*' and a==1:value=b
  if value is not None:aliases[n]=value;continue
  k=(op,a,b)
  if k in seen:aliases[n]=seen[k];continue
  seen[k]=n;aliases[n]=n;result.append((n,op,a,b))
 need(aliases['polynomial']=='polynomial','unexpected folded full output')
 return prune({n:(op,a,b) for n,op,a,b in result})

def local_proof(new,out,eps):
 V,K,e=sp.symbols('V K e');env={'aux_u_rhs':V,'R16':K,'y_aux':e}
 expr=run([(n,*v) for n,v in new.items()],env)[out]
 target=K*V**2-(K-1)*(e+eps*V)**2
 need(sp.expand(expr-target)==0,'literal local source identity')
 return str(sp.expand(expr))

def dag_proof(old,rows,out):
 # The local polynomial proof establishes the only changed factor. After that
 # cut, compare every unchanged factor and the complete output structurally.
 def expressions(source,cut):
  e={}
  for n,op,a,b in source:
   if n==cut:e[n]=('proved_auxiliary_factor',);continue
   a=('int',a) if type(a)is int else e.get(a,('input',a))
   b=('int',b) if type(b)is int else e.get(b,('input',b))
   if op in('+','*') and repr(b)<repr(a):a,b=b,a
   e[n]=(op,a,b)
  return e
 before=expressions(old,'norm_aux');after=expressions(rows,out)
 for f in FACTORS:
  if f!='norm_aux':need(before[f]==after[f],'changed nonaux factor '+f)
 need(before['polynomial']==after['polynomial'],'complete DAG cut identity')
 return 8

def dense_polynomial(rows,values,p):
 def add(a,b,s=1):
  c=[0]*max(len(a),len(b))
  for j in range(len(c)):c[j]=((a[j] if j<len(a) else 0)+s*(b[j] if j<len(b) else 0))%p
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 e={n:list(v) for n,v in values.items()}
 for n,op,a,b in rows:
  a=[a%p] if type(a)is int else e[a];b=[b%p] if type(b)is int else e[b]
  e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else-1)
 return e

def finite_positive_components():
 # Protected norm signs are algebraic modulo4; the following small exact Pell
 # instances check both inverse maps, not a complete compiled-program zero.
 residue_cases=0
 for a in range(4):
  for t in range(4):
   Delta=(a+2)**2-1;K=(Delta*t)**2
   for f in range(4):
    need((f*f-Delta*t*t)%4!=3,'strong minusone residue');residue_cases+=1
   for V in range(4):
    for y in range(4):
     need((K*V*V-(K-1)*y*y)%4!=3,'aux minusone residue');residue_cases+=1
 components=[]
 for r in range(2,8):
  # K=r^2; Pell y^2-(K/(K-1))*V^2 reformulates through
  # chi_{2K-1}(n), psi_{2K-1}(n): V=chi+(K-1)*2psi,
  # y=chi+K*2psi, whose norm is1.
  K=r*r;chi,psi=1,0;A=2*K-1
  for n in range(1,5):
   chi,psi=A*chi+(A*A-1)*psi,chi+A*psi
   V=chi+2*(K-1)*psi;y=chi+2*K*psi
   need(K*V*V-(K-1)*y*y==1,'small auxiliary Pell fixture')
   for eps in(-1,1):
    e=y-eps*V;need(e>0 and e+eps*V==y,'positive excess map')
   components.append({'r':r,'index':n,'V':V,'y':y,'difference':y-V,'sum':y+V})
 return {'mod4_cases':residue_cases,'auxiliary_component_cases':len(components),'components':components}

def verify(root):
 root=Path(root);old=source(root);base=inspect(old);need(base['operations']==87 and base['M']==48 and base['A']==39,'baseline ledger')
 need(len(cse(old))==87,'baseline simplifier changes count')
 rng=random.Random(871692026);forms=[];identities=0;numeric=0;signed=0;roundtrips=0
 degrees=[]
 for eps in(-1,1):
  for template in TEMPLATES:
   raw,new,out=rewrite(old,eps,template);local=local_proof(new,out,eps)
   rows=cse(raw);ledger=inspect(rows);need(ledger['free']==base['free'],'changed complete input interface')
   identities+=dag_proof(old,rows,out)
   for case in range(96):
    v={n:rng.randrange(-5,6) if case%2 else rng.randrange(1,6) for n in WITNESSES+['x']}
    B=(16,32,64,128)[case%4];v.update(Bm1=B-1,Kconstant=3+B*5,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3)
    V=run(old,v)['aux_u_rhs'];restored={**v,'y_aux':v['y_aux']+eps*V}
    before=run(old,restored);after=run(rows,v)
    need(after['polynomial']==before['polynomial'],'complete coordinate identity')
    for f in FACTORS:need(before[f]==after[out if f=='norm_aux' else f],'factor coordinate identity')
    need(restored['y_aux']-eps*V==v['y_aux'],'inverse coordinate identity');roundtrips+=1
    numeric+=1;signed+=case%2
   form={'epsilon':eps,'template':template,'ledger':ledger,'complete_source':rows,'auxiliary_factor_register':out,'expanded_local_factor':local,'same_integer_zero_set_under_coordinate_automorphism':True,'positive_zero_bijection':'written proof, not inferred from finite fixtures'}
   forms.append(form)
  # Complete dense source polynomials along generic affine lines independently
  # witness attainment. The general upper bound/leading proof is in the note.
  rows=forms[-6]['complete_source']
  for p in(1009,1013):
   env={n:[j+1,2*j+3] for j,n in enumerate(WITNESSES+['x'])}
   env.update({n:[v] for n,v in dict(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19).items()})
   polys=dense_polynomial(rows,env,p);pol=polys['polynomial']
   factor_degrees=[len(polys['excess_norm' if f=='norm_aux' else f])-1 for f in FACTORS]
   need(factor_degrees==[12,18,32,52,7,3,34,7],'factor degree attainment')
   need(len(pol)-1==165 and pol[-1]!=0,'degree attainment')
   top={n:v[1] for n,v in env.items() if len(v)==2}
   Q0=15*top['Jrep'];k0=top['eta']+top['zeta'];gamma=top['rho']+top['sigma']
   C0=Q0-top['F']-top['Z']-top['alpha']-8*top['x']
   predicted=(64*eps*Q0**98*top['h']**2*gamma*top['delta']**2*top['i']**4*k0**11
              *top['w']**17*top['s']**27*top['y_aux']*C0*(2*top['tau_gap']-k0))%p
   need(pol[-1]==predicted,'complete leading-form coefficient')
   degrees.append({'epsilon':eps,'prime':p,'degree':165,'factor_degrees':factor_degrees,'leading_coefficient':pol[-1],'predicted_leading_coefficient':predicted,'all_coefficients_sha256':sha(json.dumps(pol).encode())})
 need(min(f['ledger']['operations'] for f in forms)==88,'unexpected better source')
 return {'status':'PASS_NO_COMPLETE_OPERATION_IMPROVEMENT','helper_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'baseline':base,'forms':forms,
         'exact_degree':165,'degree_attainment_checks':degrees,'proof_counts':{'local_symbolic_identities':12,'unchanged_factor_and_output_DAG_identities':identities,'complete_numeric_coordinate_identities':numeric,'signed_cases':signed,'coordinate_roundtrips':roundtrips},
         'finite_components':finite_positive_components(),
         'scope':'Exactly two auxiliary-ordinate affine translations and six literal evaluation templates each. Complete ordinary input,19positive witnesses,eight units and finalizer retained. Best88/165 is dominated by established88/125; no claim of arbitrary-circuit lower bound or materialized complete universal Pell witness.'}

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
 result=json.loads(json.dumps(verify(a.root)))
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'typed receipt mismatch')
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'forms':[(f['epsilon'],f['template'],f['ledger']['operations'],f['ledger']['M'],f['ledger']['A']) for f in result['forms']]}))
