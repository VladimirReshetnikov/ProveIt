#!/usr/bin/env python3
"""Finite exact discriminant-shear schedules for the complete87 polynomial."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import sympy as sp
PINS={'complete75_asymmetric_scale_tradeoffs.py':'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660','complete75_asymmetric_scale_tradeoffs.json':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98','complete75_normalized_strong87.py':'7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8','complete75_coupled_index_linear88.py':'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
WITNESSES=['Jrep','F','alpha','zplus','f','h','i','j','o','s','w','tau_gap','eta','zeta','y_aux','Z','delta','rho','sigma']

def require(v,m):
 if not v:raise ValueError(m)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def source(root):
 for n,h in PINS.items():require(hashlib.sha256((root/n).read_bytes()).hexdigest()==h,'Pinned source changed: '+n)
 p=json.loads((root/'complete75_asymmetric_scale_tradeoffs.json').read_text())['source'][0]
 require(p['normalized'] is True and len(p['source'])==87,'Wrong source')
 return [tuple(r) for r in p['source']]

def check(rows):
 dest={n for n,*_ in rows};free={v for _,_,a,b in rows for v in (a,b) if type(v) is str and v not in dest};known=set(free)
 require(len(dest)==len(rows),'Repeated destination')
 for n,op,a,b in rows:
  require(n not in known and op in ('+','-','*'),'Bad row')
  require(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'Bad dependency');known.add(n)
 active={'polynomial'}
 for n,_,a,b in reversed(rows):
  if n in active:active.update(v for v in (a,b) if type(v) is str)
 require(dest<=active and free<=active,'Dead gate or free input')
 require(set(WITNESSES+['x'])<=free,'Lost required coordinate')
 return sorted(free)

# mode=(lambda, Horner_template, coefficient_template). No transformed positive coordinate.
MODES=[None]+[(k,f,h) for k in range(-4,5) for f in ('factored','expanded') for h in ('affine','shifted','inherited')]+[(k,'collapsed','shifted') for k in (1,3)]

def rewrite(old,main_mode,input_mode):
 for mode in (main_mode,input_mode):
  require(mode is None or type(mode) in (tuple,list) and len(mode)==3 and type(mode[0]) is int and all(type(v) is str for v in mode[1:]) and tuple(mode) in MODES[1:],'Unsupported exact shear mode')
 nodes={n:(op,a,b) for n,op,a,b in old};aliases={};serial=0
 def node(op,a,b):
  nonlocal serial
  if type(a) is int and type(b) is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='+' and a==0:return b
  if op in ('+','-') and b==0:return a
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  if op=='*' and a==-1:return node('-',0,b)
  if op=='*' and b==-1:return node('-',0,a)
  serial+=1;n='shear_'+str(serial);nodes[n]=(op,a,b);return n
 def add(a,b):return node('+',a,b)
 def sub(a,b):return node('-',a,b)
 def mul(a,b):return node('*',a,b)
 def aff(c,x,b):return add(mul(c,x),b) if b>=0 else sub(mul(c,x),-b)
 for target,mode,z,b in [('norm_main',main_mode,'R10a',lambda:add('wn2','gam')),('norm_input',input_mode,'index_rhs',lambda:add('W','modulus_multiple'))]:
  if mode is None:continue
  k,form,coefficient=mode;a='R12';base=b();u=add(a,k) if k>=0 else sub(a,-k)
  beta=base if k==0 else sub(base,mul(k,z)) if k>0 else add(base,mul(-k,z))
  two_u=add(u,u)
  if k==0:H='a4m5'
  elif k==2:H=-1
  elif coefficient=='affine':H=aff(4-2*k,a,3-k*k)
  elif coefficient=='shifted':H=aff(4-2*k,u,(k-1)*(k-3))
  else:H=sub('a4m5',mul(k,add(add(a,a),k)))
  if form=='factored':
   positive=mul(beta,add(beta,mul(two_u,z)));negative=mul(H,mul(z,z))
   value=add(positive,mul(z,z)) if H==-1 else sub(positive,negative)
  elif form=='expanded':value=add(mul(beta,beta),mul(z,sub(mul(two_u,beta),mul(H,z))))
  else:
   require(k in (1,3),'Bad collapsed template')
   value=add(mul(beta,beta),mul(two_u,mul(z,sub(beta,z) if k==1 else add(beta,z))))
  aliases[target]=value
 # Full reachable DAG with commutative common-subexpression elimination. The
 # same pass is applied to the baseline and all candidate sources.
 rows=[];memo={};cse={};busy=set()
 def get(v):
  if type(v) is int:return v
  if v in aliases:return get(aliases[v])
  if v not in nodes:return v
  if v in memo:return memo[v]
  require(v not in busy,'Cycle');busy.add(v)
  op,a,b=nodes[v];a,b=get(a),get(b)
  if op in ('+','*') and repr(b)<repr(a):a,b=b,a
  key=(op,a,b)
  if key not in cse:cse[key]=v;rows.append((v,op,a,b))
  memo[v]=cse[key];busy.remove(v);return memo[v]
 out=get('polynomial');require(out=='polynomial','Output alias changed')
 factor_exports={n:get(n) for n in FACTORS}
 require(len(rows)==len({r[0] for r in rows}),'Repeated gate')
 check(rows)
 return rows,factor_exports

def run(rows,v):
 e=dict(v)
 for n,op,a,b in rows:
  a=e[a] if type(a) is str else a;b=e[b] if type(b) is str else b
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e

def symbolic():
 a,z,b,k=sp.symbols('a z b k');H=4*a+3;D=a*a+H;u=a+k;beta=b-k*z;Hk=H-2*k*a-k*k;N=(a*z+b)**2-D*z*z
 require(sp.expand(N-(beta*(beta+2*u*z)-Hk*z*z))==0,'Factored identity')
 require(sp.expand(N-(beta*beta+z*(2*u*beta-Hk*z)))==0,'Expanded identity')
 require(sp.expand(Hk-((4-2*k)*u+(k-1)*(k-3)))==0,'Shifted coefficient')
 for shift in (1,3):
  bs=b-shift*z;us=a+shift
  collapsed=bs*bs+2*us*z*(bs-z if shift==1 else bs+z)
  require(sp.expand(N-collapsed)==0,'Collapsed identity')
 return dict(parameterized_identities=3,collapsed_identities=2)

def literal_norm_identity(rows,exports,proved):
 a,c,k,X,G,W,R=sp.symbols('a c k X G W R')
 cuts={'R12':a,'R10a':c,'index_rhs':k,'wn2':X,'gam':G,'W':W,'modulus_multiple':R}
 nodes={n:(op,l,r) for n,op,l,r in rows};memo={}
 def get(v):
  if type(v) is int:return sp.Integer(v)
  if v in cuts:return cuts[v]
  if v in memo:return memo[v]
  require(v in nodes,'Undeclared local norm leaf '+str(v))
  op,l,r=nodes[v];l,r=get(l),get(r)
  memo[v]=l+r if op=='+' else l-r if op=='-' else l*r
  return memo[v]
 delta=a*a+4*a+3
 for name,expected in [('norm_main',(a*c+X+G)**2-delta*c*c),('norm_input',(a*k+W+R)**2-delta*k*k)]:
  expression=get(exports[name]);key=(name,expression)
  if key not in proved:
   require(sp.expand(expression-expected)==0,'Literal norm cut identity failed');proved.add(key)
 return 2

def downstream_identity(old,rows,exports):
 interned={}
 def intern(x):
  if x not in interned:interned[x]=len(interned)
  return interned[x]
 def expressions(source,cuts):
  nodes={n:(op,a,b) for n,op,a,b in source};memo={}
  def get(v):
   if type(v) is int:return intern(('constant',v))
   if v in cuts:return intern(('proved_norm',cuts[v]))
   if v in memo:return memo[v]
   if v not in nodes:return intern(('variable',v))
   op,a,b=nodes[v];a,b=get(a),get(b)
   if op in ('+','*') and b<a:a,b=b,a
   memo[v]=intern((op,a,b));return memo[v]
  return get
 before=expressions(old,{'norm_main':'main','norm_input':'input'})
 after=expressions(rows,{exports['norm_main']:'main',exports['norm_input']:'input'})
 for name in FACTORS:require(before(name)==after(exports[name]),'Changed factor outside proved norm cuts')
 require(before('polynomial')==after('polynomial'),'Changed full product/finalizer after proved norm cuts')
 return 9

def verify(root):
 old=source(root);free=check(old);baseline,_=rewrite(old,None,None)
 require(len(baseline)==87 and check(baseline)==free,'Unexpected baseline CSE saving')
 sym=symbolic();records=[];best={};full=[];hist=Counter();rng=random.Random(870602);cases=0;literal_checks=0;downstream_checks=0;proved=set()
 # This exact finite search counts schedules, not arbitrary arithmetic circuits.
 for im,main in enumerate(MODES):
  for ii,inp in enumerate(MODES):
   rows,exports=rewrite(old,main,inp);require(check(rows)==free,'Changed complete interface')
   literal_checks+=literal_norm_identity(rows,exports,proved)
   downstream_checks+=downstream_identity(old,rows,exports)
   c=Counter('M' if op=='*' else 'A' for _,op,_,_ in rows);cost=len(rows);hist[cost]+=1
   mask=(main is not None)+(2*(inp is not None))
   record=dict(main_mode=main,input_mode=inp,operations=cost,M=c['M'],A=c['A'])
   records.append(record)
   if mask not in best or (cost,c['M'],im,ii)<best[mask][0]:best[mask]=((cost,c['M'],im,ii),record,rows,exports)
 # Retain literal winners for each changed-factor subset. Full numeric
 # replay of every finite form uses one positive and one signed assignment.
 for record in records:
  rows,exports=rewrite(old,record['main_mode'],record['input_mode'])
  for signed in (False,True):
   v={n:rng.randrange(-2,3) if signed else rng.randrange(1,4) for n in WITNESSES+['x']};B=(16,32,64,128)[cases%4]
   v.update(Bm1=B-1,Kconstant=3+B*5,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=4+B-1)
   left=run(old,v);right=run(rows,v)
   require(left['polynomial']==right['polynomial'],'Whole polynomial changed')
   require(all(left[n]==right[exports[n]] for n in FACTORS),'A retained factor changed');cases+=1
 for mask,(score,rec,rows,exports) in sorted(best.items()):
  full.append(dict(rec,changed_factor_mask=mask,source=rows,factor_exports=exports,output='polynomial',free_coordinates=free))
 require(min(r['operations'] for r in records)==87,'Unexpected candidate improvement')
 return dict(status='PASS_BOUNDED_NO_IMPROVEMENT',source_pins=PINS,symbolic=sym,baseline=dict(operations=87,M=48,A=39,witnesses=19),
  modes=MODES,mode_count=len(MODES),schedule_count=len(records),cost_histogram={str(k):v for k,v in sorted(hist.items())},schedules=records,
  selected_complete_sources=full,checks=dict(complete_output_cases=cases,signed_cases=cases//2,factor_identity_cases=cases*8,literal_symbolic_norm_identities=literal_checks,distinct_expanded_norm_expressions=len(proved),exact_downstream_DAG_identities=downstream_checks),
  scope='Exact all-integer polynomial identities for a finite family of discriminant shears and Horner templates. Not a general lower bound; no complete universal zero was materialized.')

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 r=json.loads(json.dumps(verify(a.root.resolve())))
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 if a.expect:require(exact(r,json.loads(a.expect.read_text())),'Receipt mismatch')
 print(r['status']);print(r['checks']);print([(x['changed_factor_mask'],x['operations'],x['M'],x['A'],x['main_mode'],x['input_mode']) for x in r['selected_complete_sources']])
